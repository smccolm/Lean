import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Statements
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.MeanValue

namespace RiemannZeta.GuthMaynard

/-- F-11: The Conditional Transfer Theorem.
    Assuming the dyadic reduction, the Type II zero bounds, the mean value theorems,
    and the Guth-Maynard large values estimate, we deduce the zero density bound. -/
def ConditionalZeroDensityTransfer : Prop :=
  ∀ (model : ZetaZeroCountModel) (detector : ZeroDetectorModel) (powerModel : ∀ k, PolynomialPowerModel detector k),
    (∀ σ T, DyadicReductionProp model σ T) →
    TypeIIBoundHypothesis model detector →
    MontgomeryMeanValue →
    GuthMaynardLargeValues →
    GuthMaynardZeroDensity (fun σ T => N model σ T)

end RiemannZeta.GuthMaynard
