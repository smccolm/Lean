import TaoTrudgianYang2025.PrimitiveTripleCount
import GuthMaynard.ArithmeticCoefficients

/-! Actual divisor sums with a uniform epsilon loss; no divisor estimate is a premise. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_divisors_cast_le_mul_card (n : ℕ) :
    (∑ g ∈ n.divisors, (g:ℝ)) ≤ (n:ℝ)*(n.divisors.card:ℝ) := by
  calc
    _ ≤ ∑ _g ∈ n.divisors, (n:ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hg).2)
        (Nat.dvd_of_mem_divisors hg)
    _ = _ := by simp [mul_comm]

theorem exists_primitive_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : ℝ), 0 < n → 0 ≤ K →
      (n.divisors.card:ℝ)+K/(n:ℝ)^2*(∑ g ∈ n.divisors, (g:ℝ)) ≤
        C*(n:ℝ)^ε*(1+K/n) := by
  obtain ⟨C,hC,hdiv⟩ := RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  refine ⟨C,hC,?_⟩
  intro n K hn hK
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (n.divisors.card:ℝ)+K/(n:ℝ)^2*((n:ℝ)*(n.divisors.card:ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_divisors_cast_le_mul_card n)
        (by positivity : 0 ≤ K/(n:ℝ)^2))
    _ = (n.divisors.card:ℝ)*(1+K/n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hdiv n hn) (by positivity)

end TaoTrudgianYang2025
