import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin

open AlgebraicCurve
theorem AlgebraicCurve.Place.mem_toValuationSubring_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin.solution
