import Dubon2026.RealLiftSecondDerivatives
import Dubon2026.RealCompactInfinitesimal

/-! # The genuine second-order right-curve operator and the original holomorphic eigenvalue -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold

/-- The displayed normalized second-order operator formed from actual geodesic, unipotent and compact right derivatives. -/
def realCasimirOperator (Φ : SL(2, ℝ) → ℂ) (g : SL(2, ℝ)) : ℂ :=
  -realRightDerivative realGeodesicCurve (realRightDerivative realGeodesicCurve Φ) g +
    realRightDerivative realGeodesicCurve Φ g -
    realRightDerivative realUpperUnipotent (realRightDerivative realUpperUnipotent Φ) g +
    realRightDerivative realUpperUnipotent (realRightDerivative realRotationCurve Φ) g

/-- Original matrix associativity makes the genuine right derivative commute exactly with every left translation. -/
theorem realRightDerivative_left_translation (c : ℝ → SL(2, ℝ))
    (Φ : SL(2, ℝ) → ℂ) (a g : SL(2, ℝ)) :
    realRightDerivative c (fun h => Φ (a * h)) g = realRightDerivative c Φ (a * g) := by
  simp only [realRightDerivative, mul_assoc]

/-- The actual second-order right-curve operator is left invariant on the original real group. -/
theorem realCasimirOperator_left_translation (Φ : SL(2, ℝ) → ℂ) (a g : SL(2, ℝ)) :
    realCasimirOperator (fun h => Φ (a * h)) g = realCasimirOperator Φ (a * g) := by
  simp only [realCasimirOperator, realRightDerivative, mul_assoc]

/-- The genuine mixed unipotent/compact derivative of the original lift uses precisely its original weight. -/
theorem realWeightLift_unipotent_rotation (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    realRightDerivative realUpperUnipotent
      (realRightDerivative realRotationCurve (realWeightLift k f)) g =
        (k : ℂ) * Complex.I * realRightDerivative realUpperUnipotent (realWeightLift k f) g := by
  have he : realRightDerivative realRotationCurve (realWeightLift k f) =
      fun h => (k : ℂ) * Complex.I * realWeightLift k f h :=
    funext (fun h => (realWeightLift_right_rotation_hasDerivAt k f h).deriv)
  rw [he]
  unfold realRightDerivative
  rw [(realWeightLift_right_unipotent_hasDerivAt k hf g).deriv]
  exact ((realWeightLift_right_unipotent_hasDerivAt k hf g).const_mul ((k : ℂ) * Complex.I)).deriv

/-- The actual original holomorphic lift has the exact k/2(1-k/2) eigenvalue for the displayed genuine second-order operator. -/
theorem realWeightLift_casimir (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    realCasimirOperator (realWeightLift k f) g =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) * realWeightLift k f g := by
  rw [realCasimirOperator, realWeightLift_unipotent_rotation k hf g]
  linear_combination -(realWeightLift_second_order_identity k hf g)

end
end Dubon2026
