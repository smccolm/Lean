import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') : ∃ v : Place K F, v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap.solution
