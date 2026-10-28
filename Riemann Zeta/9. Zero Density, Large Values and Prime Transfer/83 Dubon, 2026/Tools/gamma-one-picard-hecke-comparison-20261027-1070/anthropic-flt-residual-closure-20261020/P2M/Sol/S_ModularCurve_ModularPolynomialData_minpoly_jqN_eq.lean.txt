import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import P2M.Util
namespace P2MW.S_ModularCurve_ModularPolynomialData_minpoly_jqN_eq

open ModularCurve IntermediateField

theorem solution {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hirr : ModularCurve.PhiIrreducible data) :
    minpoly (↥ℚ⟮ModularCurve.jq⟯) (ModularCurve.jqN N) = data.toAdjoin :=
  ModularCurve.minpoly_jqN_eq_toAdjoin data hirr
