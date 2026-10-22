import Dubon2026.SourceCellWindowPerimeterSegments
import Dubon2026.SourceCellRadialRefinement

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
noncomputable section
open scoped Real
open Set

variable (D : WinData)

/-- The constructed outer region refined at all and only perimeter angles. -/
structure Win where
  /-- The original six-arc outer rectangle. -/
  B : Base D
  /-- The same radial region refined at the exact perimeter vertices. -/
  R : RadialRegion
  hq : R.q = B.R.q
  hr : R.r = B.R.r
  hK : R.K = B.R.K
  hKint : R.Kint = B.R.Kint
  hloop : R.loop = B.R.loop
  hrange : Set.range R.φs = Set.range B.R.φs ∪ (D.angles : Set ℝ)
  hN : R.N + 1 = (Set.range B.R.φs ∪ (D.angles : Set ℝ)).ncard
  hconsec : ∀ k' : Fin R.N, ∀ t ∈ Set.range B.R.φs ∪ (D.angles : Set ℝ),
    t ∉ Set.Ioo (R.φs k'.castSucc) (R.φs k'.succ)
  hsub : ∀ k' : Fin R.N, ∃ k : Fin B.R.N, R.arcIcc k' ⊆ B.R.arcIcc k

theorem exists_win : Nonempty (Win D) := by
  obtain ⟨B⟩ := D.exists_base
  obtain ⟨R, hq, hr, hK, hKint, hloop, hrange, hN, hconsec, hsub⟩ :=
    RadialRefine.exists_refine_exact B.R D.angles D.angles_bdd
  exact ⟨⟨B, R, hq, hr, hK, hKint, hloop, hrange, hN, hconsec, hsub⟩⟩

namespace Win

variable {D} (W : Win D)

theorem q_eq : W.R.q = 0 := by
  rw [W.hq, W.B.hq]

theorem K_eq : W.R.K = {z : ℂ | z.re ∈ Set.Icc D.X₀ D.X₁ ∧ z.im ∈ Set.Icc D.Y₀ D.Y₁} := by
  rw [W.hK, W.B.hK]

theorem Kint_eq : W.R.Kint = {z : ℂ | z.re ∈ Set.Ioo D.X₀ D.X₁ ∧ z.im ∈ Set.Ioo D.Y₀ D.Y₁} := by
  rw [W.hKint, W.B.hKint]

theorem N_eq : W.R.N = 2 * D.J + 4 * D.K := by
  have h := W.hN
  rw [W.B.breaks_ncard] at h
  omega

theorem two_le_N : 2 ≤ W.R.N := by
  rw [W.N_eq]
  have h1 := D.J_pos
  have h2 := D.K_pos
  omega

theorem brk_mem (i : Fin (W.R.N + 1)) : W.R.loop (W.R.φs i) ∈ D.perimPts := by
  have hmem : W.R.φs i ∈ Set.range W.B.R.φs ∪ (D.angles : Set ℝ) := by
    rw [← W.hrange]
    exact Set.mem_range_self i
  rw [Set.mem_union, Set.mem_range, Finset.mem_coe, D.mem_angles_iff] at hmem
  rw [W.hloop]
  rcases hmem with ⟨i', hi'⟩ | ⟨z, hz, hz'⟩
  · rw [← hi']
    exact W.B.brk_mem i'
  · rw [← hz', W.B.loop_ang hz]
    exact hz

theorem no_vertex_between (k : Fin W.R.N) {z : ℂ} (hz : z ∈ D.perimPts) (hzk : z ∈ W.R.arcSet k) :
    z = W.R.loop (W.R.φs k.castSucc) ∨ z = W.R.loop (W.R.φs k.succ) := by
  rw [mem_arcSet_iff] at hzk
  obtain ⟨t, ht, rfl⟩ := hzk
  rw [mem_arcIcc_iff] at ht
  rcases eq_or_lt_of_le ht.1 with h1 | h1
  · left
    rw [h1]
  rcases eq_or_lt_of_le ht.2 with h2 | h2
  · right
    rw [h2]
  exfalso
  have ht0 : 0 ≤ t := le_trans (φs_nonneg W.R _) ht.1
  have ht2 : t < 2 * π := lt_of_lt_of_le h2 (φs_le_two_pi W.R _)
  have htm : t ∈ Set.Ico 0 (2 * π) := ⟨ht0, ht2⟩
  have hloopt : W.B.R.loop t = W.R.loop t := by
    rw [W.hloop]
  have hang : t = ang (W.R.loop t) := W.B.eq_ang_of_loop_eq hz htm hloopt
  have hbrk : t ∈ Set.range W.B.R.φs ∪ (D.angles : Set ℝ) := by
    rw [Set.mem_union, Finset.mem_coe]
    right
    have h := D.ang_mem_angles hz
    rw [← hang] at h
    exact h
  have hIoo : t ∈ Set.Ioo (W.R.φs k.castSucc) (W.R.φs k.succ) := ⟨h1, h2⟩
  exact W.hconsec k t hbrk hIoo

theorem arc_data (k : Fin W.R.N) :
    ∃ (k₀ : Fin W.B.R.N) (za zb : ℂ),
      W.R.loop (W.R.φs k.castSucc) = za ∧ W.R.loop (W.R.φs k.succ) = zb ∧
      za ∈ D.perimPts ∧ zb ∈ D.perimPts ∧ za ≠ zb ∧
      W.R.arcSet k = segment ℝ za zb ∧
      (∀ z ∈ D.perimPts, z ∈ segment ℝ za zb → z = za ∨ z = zb) ∧
      za ∈ W.B.R.arcSet k₀ ∧ zb ∈ W.B.R.arcSet k₀ ∧
      za ∈ segment ℝ (W.B.R.loop (W.B.R.φs k₀.castSucc)) zb ∧
      W.R.arcIcc k ⊆ W.B.R.arcIcc k₀ := by
  obtain ⟨k₀, hsub⟩ := W.hsub k
  have ha := castSucc_mem_arcIcc W.R k
  have hb := succ_mem_arcIcc W.R k
  have hab := (φs_castSucc_lt_succ W.R k).le
  have ha' : W.R.φs k.castSucc ∈ W.B.R.arcIcc k₀ := hsub ha
  have hb' : W.R.φs k.succ ∈ W.B.R.arcIcc k₀ := hsub hb
  have hα := castSucc_mem_arcIcc W.B.R k₀
  have hαa : W.B.R.φs k₀.castSucc ≤ W.R.φs k.castSucc := ((mem_arcIcc_iff W.B.R k₀ _).mp ha').1
  have hαb : W.B.R.φs k₀.castSucc ≤ W.R.φs k.succ := ((mem_arcIcc_iff W.B.R k₀ _).mp hb').1
  have hseg : W.R.arcSet k =
      segment ℝ (W.R.loop (W.R.φs k.castSucc)) (W.R.loop (W.R.φs k.succ)) := by
    unfold Dubon2026.SourceFunctionField.CellGeometry.RadialRegion.arcSet Dubon2026.SourceFunctionField.CellGeometry.RadialRegion.arcIcc
    rw [W.hloop]
    exact W.B.seg k₀ _ _ ha' hb' hab
  have hstart : W.R.loop (W.R.φs k.castSucc) ∈
      segment ℝ (W.B.R.loop (W.B.R.φs k₀.castSucc)) (W.R.loop (W.R.φs k.succ)) := by
    have himg := W.B.seg k₀ _ _ hα hb' hαb
    rw [W.hloop, ← himg]
    have hmem : W.R.φs k.castSucc ∈ Set.Icc (W.B.R.φs k₀.castSucc) (W.R.φs k.succ) := ⟨hαa, hab⟩
    exact Set.mem_image_of_mem W.B.R.loop hmem
  have hmemA : W.R.loop (W.R.φs k.castSucc) ∈ W.B.R.arcSet k₀ := by
    rw [W.hloop]
    exact loop_mem_arcSet W.B.R k₀ ha'
  have hmemB : W.R.loop (W.R.φs k.succ) ∈ W.B.R.arcSet k₀ := by
    rw [W.hloop]
    exact loop_mem_arcSet W.B.R k₀ hb'
  have hno : ∀ z ∈ D.perimPts,
      z ∈ segment ℝ (W.R.loop (W.R.φs k.castSucc)) (W.R.loop (W.R.φs k.succ)) →
        z = W.R.loop (W.R.φs k.castSucc) ∨ z = W.R.loop (W.R.φs k.succ) := by
    intro z hz hzs
    rw [← hseg] at hzs
    exact W.no_vertex_between k hz hzs
  exact ⟨k₀, W.R.loop (W.R.φs k.castSucc), W.R.loop (W.R.φs k.succ), rfl, rfl,
    W.brk_mem k.castSucc, W.brk_mem k.succ, loop_castSucc_ne_loop_succ W.R W.two_le_N k, hseg, hno,
    hmemA, hmemB, hstart, hsub⟩


end Win

end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
