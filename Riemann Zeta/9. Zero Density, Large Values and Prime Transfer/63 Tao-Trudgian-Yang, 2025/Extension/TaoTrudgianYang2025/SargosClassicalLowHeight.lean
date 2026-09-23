import TaoTrudgianYang2025.SargosCProcessParameters
import TaoTrudgianYang2025.ExponentPairAProcess
import TaoTrudgianYang2025.ClassicalSecondDerivativePair

/-! The genuine classical A-cubed B seed used by Sargos's low-height branch. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargos_classical_aCubedB_pair : ExponentPair ((1:ℝ)/30) (26/30) := by
  have h := exponentPair_half_half.aProcess.aProcess.aProcess
  norm_num at h ⊢
  exact h

theorem sargos_classical_aCubedB_nonAsymptotic :
    IsExponentPairEstimateNonAsymptotic ((1:ℝ)/30) (26/30) :=
  isExponentPairEstimate_iff_nonAsymptotic.mp sargos_classical_aCubedB_pair.estimate

end TaoTrudgianYang2025
