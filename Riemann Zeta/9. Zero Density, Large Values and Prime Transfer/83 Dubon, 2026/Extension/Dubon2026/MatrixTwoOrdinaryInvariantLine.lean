import Dubon2026.MatrixTwoPrimitiveInvariantLine
import Dubon2026.MatrixFixedColumnFromRelations

/-! # The original ordinary matrix relations construct the entire invariant line -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G R K : Type*} [CommRing R] [Field K]

/-- The genuine two-dimensional ordinary relation operators, with a genuinely nonidentity residual element, construct an actual invertible basis in which the entire original invariant module is the first coordinate line. -/
theorem matrixTwo_invariant_line_of_ordinary_relations (r : R →+* K) [IsLocalHom r]
    (A : G → GeneralLinearGroup (Fin 2) R)
    (g₀ : G) (hA : GeneralLinearGroup.map r (A g₀) ≠ 1)
    (hrel : ∀ g, ((A g).val - 1) *
      ((A g₀).val - (GeneralLinearGroup.det (A g₀) : R) • (1 : Matrix (Fin 2) (Fin 2) R)) = 0) :
    ∃ U : GeneralLinearGroup (Fin 2) R, ∀ w : Fin 2 → R,
      (∀ g, (A g).val *ᵥ w = w) ↔ (U⁻¹.val *ᵥ w) 1 = 0 := by
  let C : Matrix (Fin 2) (Fin 2) R :=
    (A g₀).val - (GeneralLinearGroup.det (A g₀) : R) • 1
  have hCmap : C.map r = (GeneralLinearGroup.map r (A g₀)).val -
      (GeneralLinearGroup.det (GeneralLinearGroup.map r (A g₀)) : K) •
        (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp only [C, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      map_sub, map_mul, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_det,
      Units.coe_map]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hC : C.map r ≠ 0 := by
    rw [hCmap]
    exact matrixTwo_detComplement_ne_zero (GeneralLinearGroup.map r (A g₀)) hA
  obtain ⟨v, hv, hfix⟩ := matrix_exists_primitive_fixed_column r (fun g => (A g).val) C hC hrel
  exact matrixTwo_invariant_line_of_primitive_vector r A g₀ hA v hv hfix

end
end Dubon2026
