import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv

theorem Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.solution
