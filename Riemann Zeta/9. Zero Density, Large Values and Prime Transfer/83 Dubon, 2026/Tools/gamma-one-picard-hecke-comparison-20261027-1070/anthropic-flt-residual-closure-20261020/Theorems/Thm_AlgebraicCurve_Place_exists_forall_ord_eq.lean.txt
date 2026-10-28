import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_forall_ord_eq

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_forall_ord_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (Place K F)) (n : Place K F → ℤ) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ T, v.ord f = n v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_forall_ord_eq.solution
