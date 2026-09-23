import TaoTrudgianYang2025.SargosSixthLocalization

/-! Finite dyadic splitting for nonnegative integrals, with the actual scale budget. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_integral_dyadic_split (f : ℝ → ℝ) (a : ℝ) (K : ℕ)
    (hf : ∀ x, 0 ≤ f x) (hi : ∀ c d, IntegrableOn f (Icc c d)) :
    (∫ x in Icc 0 (a*2^K), f x) ≤ (∫ x in Icc 0 a, f x)+
      ∑ i ∈ Finset.range K, ∫ x in Icc (a*2^i) (2*(a*2^i)), f x := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hs := sargos_integral_Icc_split_le f (a*2^(K+1)) (a*2^K)
      hf (hi _ _) (hi _ _)
    have he : a*2^(K+1) = 2*(a*2^K) := by rw [pow_succ]; ring
    rw [he] at hs ⊢
    rw [Finset.sum_range_succ]
    linarith only [hs,ih]

theorem sargos_dyadic_scale_sum (a : ℝ) (K : ℕ) :
    ∑ i ∈ Finset.range K, a*2^i = a*(2^K-1) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

theorem sargos_dyadic_scale_budget {a A : ℝ} (ha : 0 < a) (hA : a ≤ A) :
    ∃ K : ℕ, A ≤ a*2^K ∧
      (∀ i ∈ Finset.range K, a ≤ a*2^i ∧ a*2^i ≤ A) ∧
      (∑ i ∈ Finset.range K, a*2^i) ≤ 2*A := by
  obtain ⟨n,hn₁,hn₂⟩ := exists_nat_pow_near
    ((le_div_iff₀ ha).2 (by simpa using hA) : (1:ℝ) ≤ A/a)
    (by norm_num : (1:ℝ) < 2)
  have hnA : a*2^n ≤ A := by
    have hh := (le_div_iff₀ ha).mp hn₁
    simpa only [mul_comm] using hh
  have hAend : A ≤ a*2^(n+1) := by
    have hh := (div_lt_iff₀ ha).mp hn₂
    have hh' : A < a*2^(n+1) := by simpa only [mul_comm] using hh
    exact hh'.le
  refine ⟨n+1,hAend,?_,?_⟩
  · intro i hi
    have hin : i ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    refine ⟨?_,?_⟩
    · have hp : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_left hp ha.le]
    · exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hin) ha.le).trans hnA
  · rw [sargos_dyadic_scale_sum,pow_succ]
    nlinarith only [hnA,ha]

end TaoTrudgianYang2025
