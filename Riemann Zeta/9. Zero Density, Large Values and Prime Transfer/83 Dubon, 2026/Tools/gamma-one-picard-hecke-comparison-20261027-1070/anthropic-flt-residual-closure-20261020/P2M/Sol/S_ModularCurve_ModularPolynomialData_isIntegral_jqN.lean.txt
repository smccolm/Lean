import Definitions.Def_ModularCurve_X0
import P2M.Util
namespace P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN

open ModularCurve IntermediateField

noncomputable section

theorem solution {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) :=by
  refine ⟨data.toAdjoin, data.toAdjoin_monic, ?_⟩
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

end
