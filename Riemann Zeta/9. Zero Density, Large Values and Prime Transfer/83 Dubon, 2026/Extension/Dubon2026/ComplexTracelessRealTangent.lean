import Dubon2026.ComplexTracelessProjection

/-! # The exact complexification of an original real traceless tangent -/

namespace Dubon2026

noncomputable section

/-- Removing half the original real trace and then complexifying gives the actual matrix trace projection. -/
theorem complexTracelessProjection_ofReal (a : Matrix (Fin 2) (Fin 2) ℝ) :
    complexTracelessProjection (a.map Complex.ofReal) =
      complexSl2OfRealTangent (a 0 0 - Matrix.trace a / 2) (a 1 0) (a 0 1) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTracelessProjection_val, complexSl2OfRealTangent, Matrix.trace,
      Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply]
  ring

end
end Dubon2026
