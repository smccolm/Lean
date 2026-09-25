import TaoTrudgianYang2025.AtkinsonPairGramRows
import TaoTrudgianYang2025.ClassicalSecondDerivativePair
import TaoTrudgianYang2025.ExponentPairAProcess
import TaoTrudgianYang2025.ExponentPairBProcess

/-!
# The classical pair used by the restricted-sixth-moment route

The analytic pair is derived by the proved A/B processes. The rational
identities record its future counting exponents, not a moment theorem.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem exponentPair_two_ninths_eleven_eighteenths :
    ExponentPair (2/9) (11/18) := by
  convert exponentPair_half_half.aProcess.aProcess.bProcess.aProcess.bProcess
    using 1 <;> norm_num

theorem ivic_sixth_pair_counting_coordinates :
    (((2/9 : ℝ)+(11/18))/(2/9) = 15/4) ∧
    (2*(1+2*(2/9 : ℝ)+2*(11/18))/(2/9) = 24) ∧
    ((11/18 : ℝ)/(2+4*(11/18)-2*(2/9)) = 11/72) := by
  norm_num

end TaoTrudgianYang2025
