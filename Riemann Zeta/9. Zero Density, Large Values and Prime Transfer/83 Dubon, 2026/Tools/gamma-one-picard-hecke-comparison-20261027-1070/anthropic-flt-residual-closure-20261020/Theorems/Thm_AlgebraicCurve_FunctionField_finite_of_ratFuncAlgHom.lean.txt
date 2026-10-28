import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom

theorem AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] (φ : RatFunc K →ₐ[K] F) : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.solution
