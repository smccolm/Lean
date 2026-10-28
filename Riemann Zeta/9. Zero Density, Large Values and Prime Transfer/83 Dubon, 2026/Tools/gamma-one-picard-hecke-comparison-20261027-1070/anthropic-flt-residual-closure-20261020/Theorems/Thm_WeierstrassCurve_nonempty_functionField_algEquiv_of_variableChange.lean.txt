import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

universe u
theorem WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange
    {F : Type u} [Field F] (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    Nonempty (W.toAffine.FunctionField ≃ₐ[F] (C • W).toAffine.FunctionField) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.solution
