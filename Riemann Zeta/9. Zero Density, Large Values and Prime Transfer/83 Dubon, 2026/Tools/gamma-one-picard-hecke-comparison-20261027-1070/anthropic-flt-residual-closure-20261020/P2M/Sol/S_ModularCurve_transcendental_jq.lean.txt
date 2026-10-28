import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_aeval_jq_eq_zero
import P2M.Util
namespace P2MW.S_ModularCurve_transcendental_jq

open ModularCurve IntermediateField

noncomputable section

theorem solution : Transcendental ℚ jq :=
  transcendental_iff.mpr fun _ hp => ModularCurve.aeval_jq_eq_zero hp

end
