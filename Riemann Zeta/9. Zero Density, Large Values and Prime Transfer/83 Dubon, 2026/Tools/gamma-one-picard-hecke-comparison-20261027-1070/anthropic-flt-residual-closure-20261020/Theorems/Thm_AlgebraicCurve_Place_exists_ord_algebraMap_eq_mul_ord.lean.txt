import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] (w : Place K F') (v : Place K F) (hv : v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F')) : ∃ e : ℕ, 0 < e ∧ ∀ f : F, w.ord (algebraMap F F' f) = e * v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord.solution
