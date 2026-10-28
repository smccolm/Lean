import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one

theorem ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    {ζ : L} {m : ℕ} (hm : ¬ q ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ ^ q := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one.solution
