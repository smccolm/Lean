import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem

theorem WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem {K : Type*} [Field K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] (O : ValuationSubring W.toAffine.FunctionField) (hO : O ≠ ⊤) (hK : ∀ c : K, algebraMap K W.toAffine.FunctionField c ∈ O) (hX : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) ∈ O) : ∃ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, O = (v.valuation W.toAffine.FunctionField).valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem.solution
