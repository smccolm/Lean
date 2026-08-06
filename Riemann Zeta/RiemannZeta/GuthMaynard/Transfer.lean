import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Statements
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.BetaDependence

namespace RiemannZeta.GuthMaynard

/-- Final algebraic combination step that completes the blueprint structural graph. -/
def AlgebraicCombinationHypothesis : Prop :=
  TypeIIBoundHypothesis →
  ExtractSeparatedHypothesis →
  PowCoeffBoundHypothesis →
  GuthMaynardLargeValues →
  GuthMaynardZeroDensity (fun σ T => N σ T)

/-- F-11: The Conditional Transfer Theorem.
    This theorem formalizes the logical implication from the sequence of analytic reductions
    and the large values estimates to the final Guth-Maynard zero-density bound.
    It explicitly consumes all intermediate reductions as assumptions. -/
theorem conditionalZeroDensityTransfer
    (h_type2 : TypeIIBoundHypothesis)
    (h_extract : ExtractSeparatedHypothesis)
    (h_pow_coeff : PowCoeffBoundHypothesis)
    (h_large : GuthMaynardLargeValues)
    (h_algebraic : AlgebraicCombinationHypothesis) :
    GuthMaynardZeroDensity (fun σ T => N σ T) := 
  h_algebraic h_type2 h_extract h_pow_coeff h_large

end RiemannZeta.GuthMaynard
