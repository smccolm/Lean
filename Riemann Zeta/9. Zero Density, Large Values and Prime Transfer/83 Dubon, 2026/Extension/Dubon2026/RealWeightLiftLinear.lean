import Dubon2026.RealAutomorphicLift

/-! # The genuine classical-to-real lift as an injective complex linear map -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- The literal original real lift is complex linear on actual classical functions. -/
def realWeightLiftLinear (k : ℤ) : (ℍ → ℂ) →ₗ[ℂ] (SL(2, ℝ) → ℂ) where
  toFun := realWeightLift k
  map_add' f g := by
    funext a
    simp only [realWeightLift_apply, Pi.add_apply, add_mul]
  map_smul' c f := by
    funext a
    simp only [realWeightLift_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]

/-- The genuine linear real lift is faithful on every original classical function. -/
theorem realWeightLiftLinear_injective (k : ℤ) : Function.Injective (realWeightLiftLinear k) :=
  realWeightLift_injective k

end
end Dubon2026
