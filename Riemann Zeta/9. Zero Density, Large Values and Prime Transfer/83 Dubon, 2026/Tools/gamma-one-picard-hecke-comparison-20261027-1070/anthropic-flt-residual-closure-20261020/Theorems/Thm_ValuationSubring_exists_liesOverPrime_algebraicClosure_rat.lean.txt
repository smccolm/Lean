import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat

theorem ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.solution
