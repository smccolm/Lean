import Tao2026.PublicTheorems

/-!
# Kernel-checked semantic regression gates

These assertions lock the interval endpoints, an exact finite product,
one-term/nontrivial count partitions, squarefree parity, factorial-fiber
multiplicity, and the quantified asymptotic conventions. The final assertion
consumes all four exact unconditional public contracts.
-/

namespace Tao2026
open Filter
open scoped Topology

theorem regression_interval_endpoints (N H k : ℕ) :
    k ∈ consecutiveInterval N H ↔ N < k ∧ k ≤ N + H :=
  Finset.mem_Ioc

theorem regression_interval_fixture : consecutiveProduct 2 2 = 12 := by decide

theorem regression_count_partitions (x : ℕ) :
    nontrivialBadCount x + badOneTermCount x = badCount x ∧
    nontrivialVeryBadCount x + veryBadOneTermCount x = veryBadCount x ∧
    nontrivialFactorialThreeCount x + factorialThreeOneTermCount x = factorialThreeCount x :=
  ⟨nontrivialBadCount_add_badOneTermCount x,
    nontrivialVeryBadCount_add_veryBadOneTermCount x,
    nontrivialFactorialThreeCount_add_factorialThreeOneTermCount x⟩

theorem regression_squarefree_zero_one : squarefreeComponent 0 = 1 ∧ squarefreeComponent 1 = 1 :=
  ⟨squarefreeComponent_zero, squarefreeComponent_one⟩

theorem regression_squarefree_parity (n p : ℕ) :
    p ∈ (squarefreeComponent n).primeFactors ↔ p ∈ n.primeFactors ∧ Odd (n.factorization p) :=
  mem_primeFactors_squarefreeComponent_iff

theorem regression_factorial_fiber_multiplicity (x d : ℕ) :
    (factorialSquarefreeFiberUpTo x d).card ≤ 2 :=
  factorialSquarefreeFiberUpTo_card_le_two_unconditional x d

theorem regression_asymptotic_epsilon_quantifier (f : ℕ → ℝ) (a : ℝ) :
    PowerUpperBound f a ↔ ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO atTop f (fun n : ℕ => (n : ℝ) ^ (a + ε)) := Iff.rfl

theorem regression_exact_public_contracts :
    TaoTheorem17Conclusion ∧ TaoTheorem18Conclusion ∧
      TaoTheorem19Conclusion ∧ TaoTheorem110Conclusion :=
  taoMainTheorems_unconditional

theorem regression_power_scale_both_directions (f : ℕ → ℝ) (a : ℝ) :
    PowerScale f a ↔ ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO atTop f (fun n : ℕ => (n : ℝ) ^ (a + ε)) ∧
      Asymptotics.IsBigO atTop (fun n : ℕ => (n : ℝ) ^ (a - ε)) f := Iff.rfl

theorem regression_quotient_scale_signs (f numerator scale : ℕ → ℝ) (a : ℝ) :
    QuotientPowerScale f numerator scale a ↔ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        numerator n / scale n ^ (a + ε) ≤ f n ∧
        f n ≤ numerator n / scale n ^ (a - ε) := Iff.rfl

end Tao2026
