import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_deg_ofHeightOneSpectrum_eq_one
attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

theorem WeierstrassCurve.Affine.deg_ofHeightOneSpectrum_eq_one {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve.Affine F) [IsDedekindDomain W.CoordinateRing] (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing) : (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) (F := W.FunctionField) w).deg = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_deg_ofHeightOneSpectrum_eq_one.solution
