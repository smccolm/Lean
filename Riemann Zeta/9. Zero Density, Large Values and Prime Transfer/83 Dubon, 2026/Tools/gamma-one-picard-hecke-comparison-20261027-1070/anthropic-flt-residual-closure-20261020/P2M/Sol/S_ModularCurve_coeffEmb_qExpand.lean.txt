import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_coeffEmb_qExpand

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) :=
  coeffMap_qExpand _ n x
