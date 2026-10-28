import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [IsDedekindDomain W.CoordinateRing]
    {x y : F} (h : W.Nonsingular x y) (v : AlgebraicCurve.Place F W.FunctionField)
    (hX : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ v.toValuationSubring.nonunits)
    (hY : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ v.toValuationSubring.nonunits) :
    v = placeOfPoint (Point.some x y h) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_eq_placeOfPoint_some_of_XClass_mem_nonunits_of_YClass_mem_nonunits.solution
