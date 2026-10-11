import Dubon2026.MatrixPrimitiveVectorBasis
import Dubon2026.MatrixTwoResidualInvariantAxis
import Dubon2026.MatrixConjugateFixedVectors

/-! # A primitive invariant vector yields the genuine full invariant direct summand -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R K : Type*} [CommRing R] [Field K]

/-- A primitive vector fixed by the original matrix family, together with a genuinely nonidentity residual action, supplies an actual invertible basis in which the entire original invariant module is exactly the first coordinate line. -/
theorem matrixTwo_invariant_line_of_primitive_vector (r : R →+* K) [IsLocalHom r]
    (A : G → GeneralLinearGroup (Fin 2) R)
    (g₀ : G) (hA : GeneralLinearGroup.map r (A g₀) ≠ 1)
    (v : Fin 2 → R) (hv : ∃ i, IsUnit (v i)) (hfix : ∀ g, (A g).val *ᵥ v = v) :
    ∃ U : GeneralLinearGroup (Fin 2) R, ∀ w : Fin 2 → R,
      (∀ g, (A g).val *ᵥ w = w) ↔ (U⁻¹.val *ᵥ w) 1 = 0 := by
  obtain ⟨U, hU⟩ := matrixTwo_exists_basis_column_of_unit v hv
  let B := fun g => U⁻¹ * A g * U
  let e₀ : Fin 2 → R := Pi.single 0 1
  have hcol : U.val *ᵥ e₀ = v := by
    simpa only [e₀, Matrix.mulVec_single_one] using funext hU
  have hinv : U⁻¹.val *ᵥ v = e₀ := by
    rw [← hcol, Matrix.mulVec_mulVec]
    change (U⁻¹ * U).val *ᵥ e₀ = e₀
    simp only [inv_mul_cancel, GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hfirst (g : G) : B g 0 0 = 1 ∧ B g 1 0 = 0 := by
    have hf := (matrix_conjugate_fixed_iff (A g) U v).mpr (hfix g)
    rw [hinv] at hf
    constructor
    · simpa only [e₀, Matrix.mulVec_single_one, Pi.single_eq_same] using congrFun hf 0
    · simpa only [e₀, Matrix.mulVec_single_one, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        using congrFun hf 1
  have hB : GeneralLinearGroup.map r (B g₀) ≠ 1 := by
    intro h
    have he := congrArg (fun x : GeneralLinearGroup (Fin 2) K =>
      GeneralLinearGroup.map r U * x * (GeneralLinearGroup.map r U)⁻¹) h
    apply hA
    simpa only [B, map_mul, map_inv, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, one_mul, mul_one] using he
  refine ⟨U, fun w => ?_⟩
  rw [← matrixTwo_fixed_iff_second_zero_of_residue r B hfirst g₀ hB (U⁻¹.val *ᵥ w)]
  exact (forall_congr' (fun g => matrix_conjugate_fixed_iff (A g) U w)).symm

end
end Dubon2026
