import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary

/-! # Compactness for the actual positive definite Hermitian form

The source unitary form in DUB-17 need not be the identity form.
Pinned continuous functional calculus supplies an invertible square-root
factor, reducing its archimedean isometry matrices to the actual compact
standard unitary group. No source-form identification is assumed here.
-/

namespace Dubon2026

noncomputable section

open scoped MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pinned functional calculus factors a positive definite Hermitian matrix by an invertible matrix. -/
theorem positiveHermitian_exists_unit_factor (H : Matrix ι ι ℂ) (hH : H.PosDef) :
    ∃ B : (Matrix ι ι ℂ)ˣ, star B.val * B.val = H := by
  obtain ⟨B, hB⟩ := (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit
  refine ⟨B, ?_⟩
  rw [hB, (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg

/-- The original standard complex unitary matrix set is compact in the entry topology. -/
theorem complexUnitaryMatrix_isCompact :
    IsCompact (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have hc : IsCompact {M : Matrix ι ι ℂ | ∀ i j, ‖M i j‖ ≤ 1} := by
    change IsCompact {M : ι → ι → ℂ | ∀ i j, ‖M i j‖ ≤ 1}
    convert (isCompact_univ_pi fun _ : ι =>
      isCompact_univ_pi fun _ : ι => isCompact_closedBall (0 : ℂ) 1) using 1
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
      Metric.mem_closedBall, dist_zero_right]
  refine hc.of_isClosed_subset isClosed_unitary ?_
  intro M hM i j
  exact entry_norm_bound_of_unitary hM i j

/-- The isometry matrices of a positive definite Hermitian form constitute a compact set. -/
theorem positiveHermitianUnitary_isCompact (H : Matrix ι ι ℂ) (hH : H.PosDef) :
    IsCompact {M : Matrix ι ι ℂ | star M * H * M = H} := by
  obtain ⟨B, hB⟩ := positiveHermitian_exists_unit_factor H hH
  let F : Matrix ι ι ℂ → Matrix ι ι ℂ := fun M => (B⁻¹).val * M * B.val
  have hF : Continuous F := (continuous_const.mul continuous_id).mul continuous_const
  have he : {M : Matrix ι ι ℂ | star M * H * M = H} =
      F '' (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
    ext M
    constructor
    · intro hM
      refine ⟨B.val * M * (B⁻¹).val, ?_, ?_⟩
      · apply Matrix.mem_unitaryGroup_iff'.mpr
        change star (B.val * M * (B⁻¹).val) * (B.val * M * (B⁻¹).val) = 1
        calc
          _ = star (B⁻¹).val * (star M * (star B.val * B.val) * M) * (B⁻¹).val := by
            simp only [star_mul, mul_assoc]
          _ = star (B⁻¹).val * H * (B⁻¹).val := by rw [hB, hM]
          _ = 1 := by
            rw [← hB]
            calc
              _ = star (B.val * (B⁻¹).val) * (B.val * (B⁻¹).val) := by
                simp only [star_mul, mul_assoc]
              _ = 1 := by simp
      · dsimp only [F]
        simp only [← mul_assoc, Units.inv_mul, one_mul]
        rw [mul_assoc, Units.inv_mul, mul_one]
    · rintro ⟨U, hU, rfl⟩
      change star (F U) * H * F U = H
      dsimp only [F]
      rw [← hB]
      calc
        _ = star B.val * (star U * (star ((B⁻¹).val) * (star B.val * B.val) *
            (B⁻¹).val) * U) * B.val := by simp only [star_mul, mul_assoc]
        _ = star B.val * (star U * U) * B.val := by
          have hi : star ((B⁻¹).val) * (star B.val * B.val) * (B⁻¹).val = 1 := by
            calc
              _ = star (B.val * (B⁻¹).val) * (B.val * (B⁻¹).val) := by
                simp only [star_mul, mul_assoc]
              _ = 1 := by simp
          rw [hi, mul_one]
        _ = star B.val * B.val := by rw [Unitary.star_mul_self_of_mem hU, mul_one]
  rw [he]
  exact complexUnitaryMatrix_isCompact.image hF

end
end Dubon2026
