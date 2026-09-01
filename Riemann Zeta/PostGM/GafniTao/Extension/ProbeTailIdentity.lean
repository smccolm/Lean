import GafniTao.FordNegativeExplicitIdentity
import GafniTao.FordNumericalGap
import GafniTao.FordExplicitData.Values
namespace GafniTao
noncomputable section
set_option maxRecDepth 100000000
set_option maxHeartbeats 0
example : fordBiEvalV fordTailUpperPolynomial 0 =
    fordTailAtZeroExplicit := by
  apply Polynomial.funext
  intro y
  norm_num [fordBiEvalV, fordTailUpperPolynomial,
    fordScaledTaylorPolynomial, fordTailPhasePolynomial,
    fordBiRat, fordBiY, Finset.sum_range_succ,
    fordTailAtZeroExplicit,
    fordTailAtZeroValueBlock0,
    fordTailAtZeroValueBlock1,
    fordTailAtZeroValueBlock2,
    fordTailAtZeroValueBlock3,
    fordTailAtZeroValueBlock4,
    fordTailAtZeroValueBlock5,
    fordTailAtZeroValueBlock6,
    fordTailAtZeroValueBlock7]
  ring
end
end GafniTao
