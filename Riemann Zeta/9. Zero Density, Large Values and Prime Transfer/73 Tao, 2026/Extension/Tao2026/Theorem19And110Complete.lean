import Tao2026.PrimeFreeLogShortness
import Tao2026.PublicEndpointReductions

/-!
# Unconditional Lemma 4.2 and Tao Theorems 1.9 and 1.10

Section 4 only consumes the upper scale `4 H (log N)^2 ≤ N` from the
prime-gap input. The native quantitative PNT proves this scale directly for
every sufficiently large prime-free interval. Both unchanged geometric
contradictions and the established endpoint counting chains therefore close
without assuming the stronger Baker--Harman--Pintz theorem.
-/

namespace Tao2026
open Filter
open scoped Topology
noncomputable section

theorem eventually_four_factorialPrimeScale_le_unconditional :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) = squarefreeComponent a.factorial →
      4 * factorialPrimeScale N H ≤ (N : ℝ) := by
  filter_upwards [eventually_four_mul_primeFree_length_log_sq_le] with N hshort
  intro H a hH ha haN hcomponent
  have hf3 : IsFactorialThreeInterval N H := ⟨by omega, a, ha, haN, hcomponent⟩
  have hfree : ∀ p : ℕ, N < p → p ≤ N + H → ¬p.Prime := by
    intro p hpLow hpHigh
    apply hf3.not_prime_of_mem
    simpa only [consecutiveInterval, Finset.mem_Ioc] using ⟨hpLow, hpHigh⟩
  simpa only [factorialPrimeScale, mul_assoc] using hshort H hfree

theorem taoLemma42_unconditional : TaoLemma42Conclusion := by
  intro η hη
  filter_upwards
    [eventually_not_factorialThree_of_low_primeScale_and_growth taoTheorem25Specialized_unconditional hη,
      eventually_not_factorialThree_of_large_primeScale_and_growth taoTheorem25Specialized_unconditional hη,
      eventually_four_factorialPrimeScale_le_unconditional, eventually_one_lt_log_nat] with
      N hlow hhigh hupper hlog
  intro H a hH ha haN hcomponent
  have hP : 2 ≤ factorialPrimeScale N H := by
    rw [factorialPrimeScale]
    have hHreal : (2 : ℝ) ≤ H := by exact_mod_cast hH
    have hlogSq : (1 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by nlinarith
    nlinarith
  have hfour := hupper hH ha haN hcomponent
  by_contra hbound
  have hgrowth := lt_of_not_ge hbound
  rcases le_or_gt (factorialPrimeScale N H) (Real.sqrt (2 * (N : ℝ))) with hcase | hcase
  · exact hlow hH ha haN hcomponent hcase hP hfour hgrowth
  · exact hhigh hH ha haN hcomponent hcase hP hfour hgrowth

theorem taoTheorem19_unconditional : TaoTheorem19Conclusion :=
  taoTheorem19_of_lemma42 taoLemma42_unconditional

theorem taoTheorem110_unconditional : TaoTheorem110Conclusion :=
  taoTheorem110_of_lemma42 taoLemma42_unconditional

end
end Tao2026
