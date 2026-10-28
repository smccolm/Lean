import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
namespace P2MW.S_ModularCurve_deg_jLinePlaceZero

set_option autoImplicit false

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

theorem solution : ModularCurve.jLinePlaceZero.deg = 1 := by
  unfold ModularCurve.jLinePlaceZero
  rw [Place.deg_congrRingEquiv]
  exact deg_placeOfPoint ℚ 0
