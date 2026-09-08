import GafniTao.FordExplicitData.Derived
import GafniTao.FordExplicitData.fordNegativeDiagonalValue0
import GafniTao.FordExplicitData.fordNegativeDiagonalValue1
import GafniTao.FordExplicitData.fordNegativeDiagonalValue2
import GafniTao.FordExplicitData.fordNegativeDiagonalValue3
import GafniTao.FordExplicitData.fordNegativeDiagonalValue4
import GafniTao.FordExplicitData.fordPositiveAtThreeHalvesValue0
import GafniTao.FordExplicitData.fordPositiveAtThreeHalvesValue1
import GafniTao.FordExplicitData.fordPositiveAtThreeHalvesValue2
import GafniTao.FordExplicitData.fordPositiveAtThreeHalvesValue3
import GafniTao.FordExplicitData.fordPositiveAtThreeHalvesValue4
import GafniTao.FordExplicitData.fordPositiveAtThreeHalvesValue5
import GafniTao.FordExplicitData.fordTailAtZeroValue0
import GafniTao.FordExplicitData.fordTailAtZeroValue1
import GafniTao.FordExplicitData.fordTailAtZeroValue2
import GafniTao.FordExplicitData.fordTailAtZeroValue3
import GafniTao.FordExplicitData.fordTailAtZeroValue4
import GafniTao.FordExplicitData.fordTailAtZeroValue5
import GafniTao.FordExplicitData.fordTailAtZeroValue6
import GafniTao.FordExplicitData.fordTailAtZeroValue7
import GafniTao.FordExplicitData.fordNumericalGapValue0
import GafniTao.FordExplicitData.fordNumericalGapValue1
import GafniTao.FordExplicitData.fordNumericalGapValue2
import GafniTao.FordExplicitData.fordNumericalGapValue3
import GafniTao.FordExplicitData.fordNumericalGapValue4
import GafniTao.FordExplicitData.fordNumericalGapValue5
import GafniTao.FordExplicitData.fordNumericalGapValue6
import GafniTao.FordExplicitData.fordNumericalGapValue7

namespace GafniTao

noncomputable section

def fordNegativeDiagonalExplicit : Polynomial ℚ :=
  fordNegativeDiagonalValueBlock0 +
    fordNegativeDiagonalValueBlock1 +
    fordNegativeDiagonalValueBlock2 +
    fordNegativeDiagonalValueBlock3 +
    fordNegativeDiagonalValueBlock4

def fordPositiveAtThreeHalvesExplicit : Polynomial ℚ :=
  fordPositiveAtThreeHalvesValueBlock0 +
    fordPositiveAtThreeHalvesValueBlock1 +
    fordPositiveAtThreeHalvesValueBlock2 +
    fordPositiveAtThreeHalvesValueBlock3 +
    fordPositiveAtThreeHalvesValueBlock4 +
    fordPositiveAtThreeHalvesValueBlock5

def fordTailAtZeroExplicit : Polynomial ℚ :=
  fordTailAtZeroValueBlock0 +
    fordTailAtZeroValueBlock1 +
    fordTailAtZeroValueBlock2 +
    fordTailAtZeroValueBlock3 +
    fordTailAtZeroValueBlock4 +
    fordTailAtZeroValueBlock5 +
    fordTailAtZeroValueBlock6 +
    fordTailAtZeroValueBlock7

def fordNumericalGapExplicit : Polynomial ℚ :=
  fordNumericalGapValueBlock0 +
    fordNumericalGapValueBlock1 +
    fordNumericalGapValueBlock2 +
    fordNumericalGapValueBlock3 +
    fordNumericalGapValueBlock4 +
    fordNumericalGapValueBlock5 +
    fordNumericalGapValueBlock6 +
    fordNumericalGapValueBlock7

end

end GafniTao
