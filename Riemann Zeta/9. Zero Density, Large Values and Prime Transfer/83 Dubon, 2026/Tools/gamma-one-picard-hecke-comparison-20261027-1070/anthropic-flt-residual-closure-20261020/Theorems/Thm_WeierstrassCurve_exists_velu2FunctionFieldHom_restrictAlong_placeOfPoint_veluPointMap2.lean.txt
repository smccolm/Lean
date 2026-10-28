import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

set_option autoImplicit false

theorem WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic]
    {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ' : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    [(W.veluQuotient2 x₀ y₀).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (W.veluQuotient2 x₀ y₀).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W.veluQuotient2 x₀ y₀).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W.veluQuotient2 x₀ y₀).toAffine] :
    ∃ (ι : (W.veluQuotient2 x₀ y₀).toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      ∀ P : W.toAffine.Point,
        (WeierstrassCurve.Affine.placeOfPoint P).restrictAlong ι hι
          = WeierstrassCurve.Affine.placeOfPoint
              (WeierstrassCurve.veluPointMap2 two_ne_zero hQ hgy hΔ' P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2.solution
