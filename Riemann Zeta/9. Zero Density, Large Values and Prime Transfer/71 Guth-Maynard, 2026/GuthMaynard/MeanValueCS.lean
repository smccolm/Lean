import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

lemma sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
  (∑ i ∈ s, f i)^2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i)^2 := by
  have h_CS := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => 1)
  have h_sum_one : ∑ i ∈ s, (1 : ℝ)^2 = (s.card : ℝ) := by
    simp only [one_pow, sum_const, nsmul_eq_mul, mul_one]
  have h_sum_f : ∑ i ∈ s, f i * 1 = ∑ i ∈ s, f i := by
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_one]
  rw [h_sum_f, h_sum_one] at h_CS
  rw [mul_comm] at h_CS
  exact h_CS

lemma complex_sum_sq_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
  ‖∑ i ∈ s, f i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖^2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : 0 ≤ ‖∑ i ∈ s, f i‖ := norm_nonneg _
  have h3 : 0 ≤ ∑ i ∈ s, ‖f i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h4 : ‖∑ i ∈ s, f i‖^2 ≤ (∑ i ∈ s, ‖f i‖)^2 := by
    nlinarith [h1, h2, h3]
  have h5 : (∑ i ∈ s, ‖f i‖)^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖^2 := sum_sq_le_card_mul_sum_sq s (fun i => ‖f i‖)
  exact le_trans h4 h5

end RiemannZeta.GuthMaynard
