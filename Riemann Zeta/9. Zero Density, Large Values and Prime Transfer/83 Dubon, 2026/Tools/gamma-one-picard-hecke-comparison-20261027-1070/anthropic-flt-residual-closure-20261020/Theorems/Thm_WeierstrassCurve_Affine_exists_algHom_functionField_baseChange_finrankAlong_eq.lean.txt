import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions
attribute [-simp] WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap

open AlgebraicCurve

universe u v w
theorem WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq
    {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type v) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (F' : Type w) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    (ι : (W.baseChange F).toAffine.FunctionField →ₐ[F] (W.baseChange F).toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) :
    ∃ ι' : (W.baseChange F').toAffine.FunctionField →ₐ[F'] (W.baseChange F').toAffine.FunctionField,
      ι'.toRingHom.IsIntegral ∧ ∃ hfin' : FiniteAlong F' ι', finrankAlong F' ι' = finrankAlong F ι := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.solution
