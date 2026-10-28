import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_smul_of_ne_zero

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_smul_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_smul_of_ne_zero.solution
