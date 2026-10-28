import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F)) (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.solution
