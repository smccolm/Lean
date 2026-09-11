import Tao2026.FactorialLargeSieveMaximal

open Filter Asymptotics
open scoped BigOperators Chebyshev

#check Finset.prod_dvd_prod_of_subset
#check Real.log_prod
#check Nat.mem_primeFactors
#check Nat.prod_primeFactors_of_squarefree
#check Nat.le_of_dvd
#check Real.strictMonoOn_log

namespace Tao2026

noncomputable section

theorem prod_factorialUpperHalfPrimes_dvd_squarefreeComponent_factorial
    (a : ℕ) :
    ∏ p ∈ factorialUpperHalfPrimes a, p ∣
      squarefreeComponent a.factorial := by
  rw [← Nat.prod_primeFactors_of_squarefree
    (squarefree_squarefreeComponent a.factorial)]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [mem_primeFactors_squarefreeComponent_iff]
  have hpData := Finset.mem_filter.mp hp
  have hpBounds := Finset.mem_Ioc.mp hpData.1
  have hfac := factorization_factorial_eq_one_of_half_lt
    hpData.2 hpBounds.1 hpBounds.2
  refine ⟨?_, ?_⟩
  · rw [Nat.mem_primeFactors]
    exact ⟨hpData.2, Nat.dvd_factorial hpData.2.pos hpBounds.2,
      Nat.factorial_ne_zero a⟩
  · rw [hfac]
    exact odd_one

theorem eventually_log_squarefreeComponent_factorial_lower :
    ∀ᶠ a : ℕ in atTop,
      (a : ℝ) / 4 ≤ Real.log (squarefreeComponent a.factorial : ℝ) := by
  filter_upwards [eventually_nat_factorialUpperHalfTheta_lower] with a ha
  let Q := factorialUpperHalfPrimes a
  have hprodPos : 0 < ∏ p ∈ Q, p := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hcomponentPos : 0 < squarefreeComponent a.factorial :=
    squarefreeComponent_pos_of_positive ⟨a.factorial, Nat.factorial_pos a⟩
  have hprodLe : ∏ p ∈ Q, p ≤ squarefreeComponent a.factorial :=
    Nat.le_of_dvd hcomponentPos
      (prod_factorialUpperHalfPrimes_dvd_squarefreeComponent_factorial a)
  have hlogLe : Real.log (∏ p ∈ Q, p : ℕ) ≤
      Real.log (squarefreeComponent a.factorial : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show (0 : ℝ) < (∏ p ∈ Q, p : ℕ)
      exact_mod_cast hprodPos
    · show (0 : ℝ) < squarefreeComponent a.factorial
      exact_mod_cast hcomponentPos
    · exact_mod_cast hprodLe
  calc
    (a : ℝ) / 4 ≤
        Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) := ha
    _ = ∑ p ∈ Q, Real.log p := by
      symm
      exact sum_log_factorialUpperHalfPrimes_eq_theta_sub a
    _ = Real.log (∏ p ∈ Q, p : ℕ) := by
      symm
      push_cast
      rw [Real.log_prod]
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    _ ≤ Real.log (squarefreeComponent a.factorial : ℝ) := hlogLe

end

end Tao2026
