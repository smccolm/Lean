import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (Polynomial.C Polynomial.X))
      ∉ (placeOfPoint (0 : W.Point)).toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero.solution
