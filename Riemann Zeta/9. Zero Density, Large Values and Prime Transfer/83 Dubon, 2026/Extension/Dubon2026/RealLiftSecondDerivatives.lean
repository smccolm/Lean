import Dubon2026.HolomorphicCurveJets
import Dubon2026.RealOneParameterDerivatives

/-! # Actual second real-group derivatives of the original holomorphic lift -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Manifold

/-- The literal second unipotent derivative is the second complex derivative of the original slash transform. -/
theorem realWeightLift_unipotent_second (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    realRightDerivative realUpperUnipotent
      (realRightDerivative realUpperUnipotent (realWeightLift k f)) g =
        deriv (deriv ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex)) Complex.I := by
  rw [realRightDerivative_twice _ realUpperUnipotent_add]
  simp_rw [realWeightLift_right_unipotent_formula]
  exact holomorphic_horizontal_second
    (UpperHalfPlane.mdifferentiable_iff.mp (hf.slash k (mapGL ℝ g)))

/-- The genuine second geodesic derivative retains all original weight and complex-derivative terms. -/
theorem realWeightLift_geodesic_second (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    realRightDerivative realGeodesicCurve
      (realRightDerivative realGeodesicCurve (realWeightLift k f)) g =
        ((k : ℂ) / 2) ^ 2 * realWeightLift k f g +
          (k + 1) * Complex.I * deriv ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) Complex.I -
            deriv (deriv ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex)) Complex.I := by
  rw [realRightDerivative_twice _ realGeodesicCurve_add]
  have he : (fun t : ℝ => realWeightLift k f (g * realGeodesicCurve t)) =
      holomorphicWeightedExponential ((k : ℝ) / 2) ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) := by
    funext t
    rw [realWeightLift_right_geodesic_formula]
    simp only [holomorphicWeightedExponential, mul_comm]
  rw [he, holomorphicWeightedExponential_second _
    (UpperHalfPlane.mdifferentiable_iff.mp (hf.slash k (mapGL ℝ g)))]
  have hi : ofComplex Complex.I = I := ofComplex_apply I
  simp only [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat,
    Function.comp_def, hi, realWeightLift]
  ring

/-- The original lift satisfies the exact weight-restricted second-order relation along genuine right matrix curves. -/
theorem realWeightLift_second_order_identity (k : ℤ) {f : ℍ → ℂ}
    (hf : MDiff f) (g : SL(2, ℝ)) :
    realRightDerivative realGeodesicCurve
        (realRightDerivative realGeodesicCurve (realWeightLift k f)) g -
      realRightDerivative realGeodesicCurve (realWeightLift k f) g +
      realRightDerivative realUpperUnipotent
        (realRightDerivative realUpperUnipotent (realWeightLift k f)) g -
      (k : ℂ) * Complex.I * realRightDerivative realUpperUnipotent (realWeightLift k f) g =
        ((k : ℂ) / 2) * ((k : ℂ) / 2 - 1) * realWeightLift k f g := by
  rw [realWeightLift_geodesic_second k hf g, realWeightLift_unipotent_second k hf g]
  unfold realRightDerivative
  rw [(realWeightLift_right_geodesic_hasDerivAt k hf g).deriv,
    (realWeightLift_right_unipotent_hasDerivAt k hf g).deriv]
  ring

end
end Dubon2026
