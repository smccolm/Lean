import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_eq_valuationSubring_of_X_not_mem

theorem WeierstrassCurve.Affine.FunctionField.eq_valuationSubring_of_X_not_mem {K : Type*} [Field K] (W : WeierstrassCurve K) (O : ValuationSubring W.toAffine.FunctionField) (hK : ∀ c : K, algebraMap K W.toAffine.FunctionField c ∈ O) (hX : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) ∉ O) (v : Valuation W.toAffine.FunctionField (WithZero (Multiplicative ℤ))) (hv : ∀ f : W.toAffine.CoordinateRing, f ≠ 0 → v (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField f) = WithZero.exp ((Algebra.norm (Polynomial K) f).natDegree : ℤ)) : O = v.valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_eq_valuationSubring_of_X_not_mem.solution
