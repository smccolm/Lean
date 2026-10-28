import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm

theorem WeierstrassCurve.Affine.FunctionField.exists_valuation_eq_exp_natDegree_norm {K : Type*} [Field K] (W : WeierstrassCurve K) : ∃ v : Valuation W.toAffine.FunctionField (WithZero (Multiplicative ℤ)), ∀ f : W.toAffine.CoordinateRing, f ≠ 0 → v (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField f) = WithZero.exp ((Algebra.norm (Polynomial K) f).natDegree : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm.solution
