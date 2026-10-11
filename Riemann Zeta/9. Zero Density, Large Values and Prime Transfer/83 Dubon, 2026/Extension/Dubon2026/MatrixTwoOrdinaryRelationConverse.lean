import Dubon2026.MatrixTwoOrdinaryInvariantLine

/-! # A genuine original invariant-line splitting implies the ordinary matrix relations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R : Type*} [CommRing R]

private theorem conjugate_first_column_of_fixed_line
    (A : G → GeneralLinearGroup (Fin 2) R) (U : GeneralLinearGroup (Fin 2) R)
    (hU : ∀ w : Fin 2 → R,
      (∀ g, (A g).val *ᵥ w = w) ↔ (U⁻¹.val *ᵥ w) 1 = 0) (g : G) :
    (U⁻¹ * A g * U) 0 0 = 1 ∧ (U⁻¹ * A g * U) 1 0 = 0 := by
  let e₀ : Fin 2 → R := Pi.single 0 1
  let v := U.val *ᵥ e₀
  have hinv : U⁻¹.val *ᵥ v = e₀ := by
    change U⁻¹.val *ᵥ (U.val *ᵥ e₀) = e₀
    rw [Matrix.mulVec_mulVec]
    change (U⁻¹ * U).val *ᵥ e₀ = e₀
    simp only [inv_mul_cancel, GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hv : ∀ g, (A g).val *ᵥ v = v := (hU v).mpr (by rw [hinv]; simp [e₀])
  have hf := (matrix_conjugate_fixed_iff (A g) U v).mpr (hv g)
  rw [hinv] at hf
  constructor
  · simpa only [e₀, Matrix.mulVec_single_one, Pi.single_eq_same] using congrFun hf 0
  · simpa only [e₀, Matrix.mulVec_single_one, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      using congrFun hf 1

private theorem detComplement_maps_coordinate_line
    (B U : GeneralLinearGroup (Fin 2) R)
    (hB : (U⁻¹ * B * U) 0 0 = 1 ∧ (U⁻¹ * B * U) 1 0 = 0)
    (w : Fin 2 → R) :
    (U⁻¹.val *ᵥ ((B.val - (GeneralLinearGroup.det B : R) •
      (1 : Matrix (Fin 2) (Fin 2) R)) *ᵥ w)) 1 = 0 := by
  let V := U⁻¹ * B * U
  let d : R := GeneralLinearGroup.det B
  have hV : V 0 0 = 1 ∧ V 1 0 = 0 := hB
  have hdet : GeneralLinearGroup.det V = GeneralLinearGroup.det B := by
    simp only [V, map_mul, map_inv]
    rw [mul_comm (GeneralLinearGroup.det U)⁻¹ (GeneralLinearGroup.det B),
      mul_assoc, inv_mul_cancel, mul_one]
  have hd : V 1 1 = d := by
    have he := congrArg (fun x : Rˣ => (x : R)) hdet
    change V.val.det = d at he
    simpa only [Matrix.det_fin_two, hV.1, hV.2, one_mul, mul_zero, sub_zero] using he
  have hcomm : U⁻¹.val * (B.val - d • (1 : Matrix (Fin 2) (Fin 2) R)) =
      (V.val - d • (1 : Matrix (Fin 2) (Fin 2) R)) * U⁻¹.val := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    congr 1
    change (U⁻¹ * B).val = (V * U⁻¹).val
    simp only [V, mul_assoc, mul_inv_cancel, mul_one]
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hV.2, hd]

/-- If the entire original invariant module is the first coordinate line in a genuine invertible basis, every original ordinary matrix relation vanishes. This is the reverse direction of the actual relation criterion. -/
theorem matrixTwo_ordinary_relations_of_invariant_line
    (A : G → GeneralLinearGroup (Fin 2) R) (U : GeneralLinearGroup (Fin 2) R)
    (hU : ∀ w : Fin 2 → R,
      (∀ g, (A g).val *ᵥ w = w) ↔ (U⁻¹.val *ᵥ w) 1 = 0) (g₀ g : G) :
    ((A g).val - 1) *
      ((A g₀).val - (GeneralLinearGroup.det (A g₀) : R) •
        (1 : Matrix (Fin 2) (Fin 2) R)) = 0 := by
  let C := (A g₀).val - (GeneralLinearGroup.det (A g₀) : R) •
    (1 : Matrix (Fin 2) (Fin 2) R)
  have hC (w : Fin 2 → R) : (A g).val *ᵥ (C *ᵥ w) = C *ᵥ w :=
    (hU (C *ᵥ w)).mpr (detComplement_maps_coordinate_line (A g₀) U
      (conjugate_first_column_of_fixed_line A U hU g₀) w) g
  have hmul : (A g).val * C = C := by
    ext i j
    have he := congrFun (hC (Pi.single j 1)) i
    simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] using he
  change ((A g).val - 1) * C = 0
  rw [sub_mul, one_mul, hmul, sub_self]

end
end Dubon2026
