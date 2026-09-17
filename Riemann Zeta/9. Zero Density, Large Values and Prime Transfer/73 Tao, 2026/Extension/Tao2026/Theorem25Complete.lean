import Tao2026.ClassicalQuantitativePNT
import Tao2026.VinogradovIKComplete
import Tao2026.VeryBadAsymptotics

/-!
# Unconditional specialized Theorem 2.5

The classical quantitative prime number theorem and the source-faithful
Iwaniec--Kowalski/Vinogradov estimate discharge the two analytic inputs of the
specialized prime-equidistribution theorem.  The established Lemma 3.1
reduction then gives Tao's complete Theorem 1.8.
-/

namespace Tao2026

/-- The exact specialized Theorem 2.5 conclusion, with no hypotheses. -/
theorem taoTheorem25Specialized_unconditional :
    TaoTheorem25SpecializedConclusion :=
  taoTheorem25Specialized_of_vinogradov
    vinogradovExponentialSumEstimate_unconditional

/-- Tao's literal Theorem 1.8 conclusion, with no hypotheses. -/
theorem taoTheorem18_unconditional : TaoTheorem18Conclusion :=
  taoTheorem18_of_taoTheorem25Specialized
    taoTheorem25Specialized_unconditional

end Tao2026
