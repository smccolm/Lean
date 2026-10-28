import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental

theorem Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.solution
