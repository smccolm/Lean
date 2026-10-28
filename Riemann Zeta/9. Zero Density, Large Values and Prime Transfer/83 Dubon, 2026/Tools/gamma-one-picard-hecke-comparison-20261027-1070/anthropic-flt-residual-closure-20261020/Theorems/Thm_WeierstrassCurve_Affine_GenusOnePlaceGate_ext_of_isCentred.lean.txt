import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePic0
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred
attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem WeierstrassCurve.Affine.GenusOnePlaceGate.ext_of_isCentred
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [IsDedekindDomain W.CoordinateRing]
    (g₁ g₂ : WeierstrassCurve.Affine.GenusOnePlaceGate W)
    (h₁ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₁)
    (h₂ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₂) :
    g₁ = g₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred.solution
