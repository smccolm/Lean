import Dubon2026.RealWeightLiftLinear
import Dubon2026.RealPositiveUnitaryLift

/-! # Exact original positive-matrix slash normalization along the genuine real orbit -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- Left multiplication by a genuine positive real matrix is the actual classical slash translate with its exact determinant-root correction. -/
theorem realPositiveUnitaryLift_left_slash (k : ℤ) (f : ℍ → ℂ) (a : GL(2, ℝ)⁺) (g : SL(2, ℝ)) :
    realPositiveUnitaryLift k f (a * toGLPos g) =
      (realPositiveDetRoot a : ℂ) ^ (2 - k) * realWeightLift k (f ∣[k] a.val) g := by
  rw [realPositiveUnitaryLift_slash_correction, realPositiveDetRoot_mul]
  have hg : realPositiveDetRoot (toGLPos g) = 1 := by simp [realPositiveDetRoot]
  rw [hg, mul_one]
  change (realPositiveDetRoot a : ℂ) ^ (2 - k) * (f ∣[k] (a.val * toGL g)) I = _
  rw [SlashAction.slash_mul]
  rfl

end
end Dubon2026
