import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
namespace P2MW.S_ModularCurve_deg_jLinePlace1728

set_option autoImplicit false

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

theorem solution : ModularCurve.jLinePlace1728.deg = 1 := by
  unfold ModularCurve.jLinePlace1728
  rw [Place.deg_congrRingEquiv]
  exact deg_placeOfPoint ℚ 1728
