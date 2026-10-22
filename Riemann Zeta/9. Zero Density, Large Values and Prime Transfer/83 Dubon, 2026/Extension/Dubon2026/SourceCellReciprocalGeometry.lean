import Dubon2026.SourceCellReciprocalRegion
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! DUB-17/18 -> original Abel-Jacobi -> exterior cells of the actual dissection.
Reciprocal radial regions turn the exterior of the finite grid window into
bounded pole-chart regions, with exact reversed arc indexing and images.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Native inverse-order equivalences and existing radial periodicity are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialRecip
noncomputable section
open Set
open scoped Real
variable (R : RadialRegion)

private theorem r_arg_inv (w : ℂ) : R.r (Complex.arg w⁻¹) = R.r (-Complex.arg w) := by
  rw [Complex.arg_inv]
  split_ifs with h
  · rw [h]
    have h1 := R.hper (-Real.pi)
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [h2] at h1
    rw [← h1]
  · rfl

theorem mem_K_iff (hq : R.q = 0) {w : ℂ} (hw : w ≠ 0) : w ∈ (recip R).K ↔ w⁻¹ ∉ R.Kint := by
  have hK : w ∈ (recip R).K ↔ ‖w‖ ≤ (R.r (-Complex.arg w))⁻¹ := by
    show ‖w - 0‖ ≤ (R.r (-Complex.arg (w - 0)))⁻¹ ↔ _
    rw [sub_zero]
  have hKint : w⁻¹ ∉ R.Kint ↔ R.r (-Complex.arg w) ≤ ‖w‖⁻¹ := by
    show ¬ (‖w⁻¹ - R.q‖ < R.r (Complex.arg (w⁻¹ - R.q))) ↔ _
    rw [hq, sub_zero, not_lt, r_arg_inv R w, norm_inv]
  rw [hK, hKint]
  constructor
  · intro h
    exact (le_inv_comm₀ (norm_pos_iff.mpr hw) (R.hpos _)).mp h
  · intro h
    exact (le_inv_comm₀ (R.hpos _) (norm_pos_iff.mpr hw)).mp h

theorem mem_Kint_iff (hq : R.q = 0) {w : ℂ} (hw : w ≠ 0) :
    w ∈ (recip R).Kint ↔ w⁻¹ ∉ R.K := by
  have hKint : w ∈ (recip R).Kint ↔ ‖w‖ < (R.r (-Complex.arg w))⁻¹ := by
    show ‖w - 0‖ < (R.r (-Complex.arg (w - 0)))⁻¹ ↔ _
    rw [sub_zero]
  have hK : w⁻¹ ∉ R.K ↔ R.r (-Complex.arg w) < ‖w‖⁻¹ := by
    show ¬ (‖w⁻¹ - R.q‖ ≤ R.r (Complex.arg (w⁻¹ - R.q))) ↔ _
    rw [hq, sub_zero, not_le, r_arg_inv R w, norm_inv]
  rw [hKint, hK]
  constructor
  · intro h
    exact (lt_inv_comm₀ (norm_pos_iff.mpr hw) (R.hpos _)).mp h
  · intro h
    exact (lt_inv_comm₀ (R.hpos _) (norm_pos_iff.mpr hw)).mp h

theorem image_inv_arcSet (hq : R.q = 0) (k : Fin R.N) :
    (fun w : ℂ => w⁻¹) '' (recip R).arcSet (idx R (Fin.rev k)) = R.arcSet k := by
  have hI1 : (recip R).φs (Fin.castSucc (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.succ := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.castSucc (Fin.rev k))) = _
    rw [Fin.rev_castSucc, Fin.rev_rev]
  have hI2 : (recip R).φs (Fin.succ (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.castSucc := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.succ (Fin.rev k))) = _
    rw [Fin.rev_succ, Fin.rev_rev]
  simp only [RadialRegion.arcSet, RadialRegion.arcIcc, hI1, hI2, Set.image_image, loop_recip R hq]
  ext w
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨hφ1, hφ2⟩ := hφ
    refine ⟨2 * Real.pi - φ, ⟨by linarith, by linarith⟩, ?_⟩
    show R.loop (2 * Real.pi - φ) = R.loop (-φ)
    exact loop_two_pi_sub R φ
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨hψ1, hψ2⟩ := hψ
    refine ⟨2 * Real.pi - ψ, ⟨by linarith, by linarith⟩, ?_⟩
    show R.loop (-(2 * Real.pi - ψ)) = R.loop ψ
    have h := loop_two_pi_sub R (2 * Real.pi - ψ)
    rw [show 2 * Real.pi - (2 * Real.pi - ψ) = ψ by ring] at h
    exact h.symm

theorem arcIcc_recip_idx_rev (k : Fin R.N) :
    (recip R).arcIcc (idx R (Fin.rev k)) = (fun t : ℝ => 2 * Real.pi - t) '' R.arcIcc k := by
  have hI1 : (recip R).φs (Fin.castSucc (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.succ := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.castSucc (Fin.rev k))) = _
    rw [Fin.rev_castSucc, Fin.rev_rev]
  have hI2 : (recip R).φs (Fin.succ (idx R (Fin.rev k))) = 2 * Real.pi - R.φs k.castSucc := by
    show 2 * Real.pi - R.φs (Fin.rev (Fin.succ (Fin.rev k))) = _
    rw [Fin.rev_succ, Fin.rev_rev]
  simp only [RadialRegion.arcIcc, hI1, hI2]
  ext t
  constructor
  · intro ht
    obtain ⟨ht1, ht2⟩ := ht
    refine ⟨2 * Real.pi - t, ⟨by linarith, by linarith⟩, ?_⟩
    show 2 * Real.pi - (2 * Real.pi - t) = t
    ring
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2⟩ := hx
    show 2 * Real.pi - x ∈ Set.Icc (2 * Real.pi - R.φs k.succ) (2 * Real.pi - R.φs k.castSucc)
    exact ⟨by linarith, by linarith⟩

/- As constructed below. -/
/-- The reversed arc-index bijection for reciprocal regions. -/
def arcEquiv : Fin R.N ≃ Fin (recip R).N where
  toFun k := idx R (Fin.rev k)
  invFun j := Fin.rev (unidx R j)
  left_inv k := by
    show Fin.rev (Fin.rev k) = k
    exact Fin.rev_rev k
  right_inv j := by
    show Fin.rev (Fin.rev (unidx R j)) = unidx R j
    exact Fin.rev_rev _

theorem arcEquiv_apply (k : Fin R.N) : arcEquiv R k = idx R (Fin.rev k) := rfl

theorem arcIcc_recip_arcEquiv (k : Fin R.N) :
    (recip R).arcIcc (arcEquiv R k) = (fun t : ℝ => 2 * Real.pi - t) '' R.arcIcc k := by
  rw [arcEquiv_apply R k]
  exact arcIcc_recip_idx_rev R k

theorem image_inv_arcSet_arcEquiv (hq : R.q = 0) (k : Fin R.N) :
    (fun w : ℂ => w⁻¹) '' (recip R).arcSet (arcEquiv R k) = R.arcSet k := by
  rw [arcEquiv_apply R k]
  exact image_inv_arcSet R hq k

theorem exists_recip (R : RadialRegion) (hq : R.q = 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) := by
  exact ⟨recip R, recip_q R, recip_N R, zero_mem_Kint R, fun w hw => mem_K_iff R hq hw,
    fun w hw => mem_Kint_iff R hq hw, loop_recip_eq R hq, arcEquiv R, arcIcc_recip_arcEquiv R,
    image_inv_arcSet_arcEquiv R hq⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.RadialRecip
