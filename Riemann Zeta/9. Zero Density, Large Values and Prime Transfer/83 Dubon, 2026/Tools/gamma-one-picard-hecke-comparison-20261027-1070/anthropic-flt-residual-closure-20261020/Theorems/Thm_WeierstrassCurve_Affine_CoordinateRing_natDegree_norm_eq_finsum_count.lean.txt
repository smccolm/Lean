import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count

open scoped nonZeroDivisors
theorem WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_eq_finsum_count {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) : ((Algebra.norm (Polynomial K) a).natDegree : ℤ) = ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, FractionalIdeal.count W.toAffine.FunctionField v (FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_natDegree_norm_eq_finsum_count.solution
