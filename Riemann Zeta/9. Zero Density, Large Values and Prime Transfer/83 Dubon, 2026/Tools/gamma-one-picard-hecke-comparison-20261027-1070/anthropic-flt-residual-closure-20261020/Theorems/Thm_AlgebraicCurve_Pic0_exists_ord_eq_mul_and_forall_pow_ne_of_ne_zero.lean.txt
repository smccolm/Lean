import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) (hx0 : x ≠ 0) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) ∧
        ∀ b : F, b ^ n ≠ f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.solution
