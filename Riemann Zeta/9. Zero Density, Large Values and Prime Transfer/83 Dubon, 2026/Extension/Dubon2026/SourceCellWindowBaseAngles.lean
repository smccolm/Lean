import Dubon2026.SourceCellWindowBase

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData.Base
noncomputable section
open scoped Real
open Set

variable {D : WinData} (B : Base D)

theorem perim_mem_K {z : ℂ} (hz : z ∈ D.perimPts) : z ∈ B.R.K := by
  rw [B.hK, Set.mem_setOf_eq]
  exact D.perimPts_mem_closed hz

theorem perim_not_mem_Kint {z : ℂ} (hz : z ∈ D.perimPts) : z ∉ B.R.Kint := by
  rw [B.hKint, Set.mem_setOf_eq]
  exact D.perimPts_not_mem_open hz

theorem loop_ang {z : ℂ} (hz : z ∈ D.perimPts) : B.R.loop (ang z) = z :=
  B.bdry z (B.perim_mem_K hz) (B.perim_not_mem_Kint hz)

theorem eq_ang_of_loop_eq {z : ℂ} (hz : z ∈ D.perimPts) {t : ℝ} (ht : t ∈ Set.Ico 0 (2 * π))
    (h : B.R.loop t = z) : t = ang z := by
  have h' : B.R.loop t = B.R.loop (ang z) := by
    rw [h, B.loop_ang hz]
  exact loop_injOn_Ico B.R ht (ang_mem z) h'

include B in

theorem ang_inj {z z' : ℂ} (hz : z ∈ D.perimPts) (hz' : z' ∈ D.perimPts) (h : ang z = ang z') :
    z = z' :=
  calc z = B.R.loop (ang z) := (B.loop_ang hz).symm
    _ = B.R.loop (ang z') := by rw [h]
    _ = z' := B.loop_ang hz'

include B in

theorem angles_card : D.angles.card = D.perimPts.card := by
  unfold WinData.angles
  refine Finset.card_image_of_injOn ?_
  intro z hz z' hz' h
  exact B.ang_inj (Finset.mem_coe.mp hz) (Finset.mem_coe.mp hz') h

theorem brk_mem (i : Fin (B.R.N + 1)) : B.R.loop (B.R.φs i) ∈ D.perimPts := by
  have hi : i.val < 7 := by
    have h := i.isLt
    have h6 := B.hN
    omega
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
      i.val = 6) with h | h | h | h | h | h | h
  · rw [B.brk0 i h]
    exact D.right_zero_mem_perimPts
  · rw [B.brk1 i h]
    exact D.corner_X₁Y₁_mem
  · rw [B.brk2 i h]
    exact D.corner_X₀Y₁_mem
  · rw [B.brk3 i h]
    exact D.split_X₀_mem
  · rw [B.brk4 i h]
    exact D.corner_X₀Y₀_mem
  · rw [B.brk5 i h]
    exact D.corner_X₁Y₀_mem
  · rw [B.brk6 i h]
    exact D.right_zero_mem_perimPts

theorem φs_mem_angles_or (i : Fin (B.R.N + 1)) : B.R.φs i ∈ D.angles ∨ B.R.φs i = 2 * π := by
  rcases eq_or_lt_of_le (φs_le_two_pi B.R i) with h | h
  · exact Or.inr h
  · left
    have h' := B.eq_ang_of_loop_eq (B.brk_mem i) ⟨φs_nonneg B.R i, h⟩ rfl
    have h'' := D.ang_mem_angles (B.brk_mem i)
    rw [← h'] at h''
    exact h''

theorem breaks_eq :
    Set.range B.R.φs ∪ (D.angles : Set ℝ) = ((insert (2 * π) D.angles : Finset ℝ) : Set ℝ) := by
  ext t
  simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_union, Set.mem_range, Finset.mem_coe]
  constructor
  · rintro (⟨i, rfl⟩ | ht)
    · rcases B.φs_mem_angles_or i with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact Or.inr ht
  · rintro (rfl | ht)
    · exact Or.inl ⟨Fin.last _, B.R.hφN⟩
    · exact Or.inr ht

theorem breaks_ncard :
    (Set.range B.R.φs ∪ (D.angles : Set ℝ)).ncard = 2 * D.J + 4 * D.K + 1 := by
  rw [B.breaks_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem D.two_pi_not_mem_angles,
    B.angles_card, D.perimPts_card]


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData.Base
