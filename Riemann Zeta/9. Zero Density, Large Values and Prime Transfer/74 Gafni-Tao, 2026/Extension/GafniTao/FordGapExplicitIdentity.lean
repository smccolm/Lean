import GafniTao.FordTailExplicitIdentity
import GafniTao.FordExplicitData.GapCertificate

/-!
# Exact source identity for Ford's numerical gap polynomial

This module connects every source-defined piece of the normalized-integral
majorant to the generated exact rational gap polynomial.  The final equality
is an exact polynomial identity, not a numerical approximation.
-/

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

theorem fordNumericalCompactPolynomial_eq_explicit :
    fordNumericalCompactPolynomial =
      fordNegativeDiagonalExplicit + fordPositiveAtThreeHalvesExplicit := by
  unfold fordNumericalCompactPolynomial
  rw [fordNegativeIntegralDiagonal_source_eq_explicit,
    fordPositiveIntegral_source_eq_explicit]

theorem fordNumericalTailPolynomial_eq_explicit :
    fordNumericalTailPolynomial = fordTailAtZeroExplicit := by
  exact fordTailAtZero_source_eq_explicit

theorem fordNumericalGap_eq_explicit :
    fordNumericalGap = fordNumericalGapExplicit := by
  rw [fordNumericalGap, fordNumericalNumerator,
    fordNumericalCompactPolynomial_eq_explicit,
    fordNumericalTailPolynomial_eq_explicit]
  apply Polynomial.funext
  intro y
  norm_num [fordNumericalTarget, fordNumericalDenominator,
    fordNegativeDiagonalExplicit, fordPositiveAtThreeHalvesExplicit,
    fordTailAtZeroExplicit, fordNumericalGapExplicit,
    fordNegativeDiagonalValueBlock0,
    fordNegativeDiagonalValueBlock1,
    fordNegativeDiagonalValueBlock2,
    fordNegativeDiagonalValueBlock3,
    fordNegativeDiagonalValueBlock4,
    fordPositiveAtThreeHalvesValueBlock0,
    fordPositiveAtThreeHalvesValueBlock1,
    fordPositiveAtThreeHalvesValueBlock2,
    fordPositiveAtThreeHalvesValueBlock3,
    fordPositiveAtThreeHalvesValueBlock4,
    fordPositiveAtThreeHalvesValueBlock5,
    fordTailAtZeroValueBlock0,
    fordTailAtZeroValueBlock1,
    fordTailAtZeroValueBlock2,
    fordTailAtZeroValueBlock3,
    fordTailAtZeroValueBlock4,
    fordTailAtZeroValueBlock5,
    fordTailAtZeroValueBlock6,
    fordTailAtZeroValueBlock7,
    fordNumericalGapValueBlock0,
    fordNumericalGapValueBlock1,
    fordNumericalGapValueBlock2,
    fordNumericalGapValueBlock3,
    fordNumericalGapValueBlock4,
    fordNumericalGapValueBlock5,
    fordNumericalGapValueBlock6,
    fordNumericalGapValueBlock7]
  ring

end

end GafniTao
