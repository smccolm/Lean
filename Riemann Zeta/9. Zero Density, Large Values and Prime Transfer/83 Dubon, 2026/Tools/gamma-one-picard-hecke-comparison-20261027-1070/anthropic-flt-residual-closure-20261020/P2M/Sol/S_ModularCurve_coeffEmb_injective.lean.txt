import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_coeffMap_injective
import P2M.Util
namespace P2MW.S_ModularCurve_coeffEmb_injective

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) :=
  coeffMap_injective (FaithfulSMul.algebraMap_injective ℚ L)
