import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! A finite second/fourth-moment lower-tail estimate, with exact multiplicities. -/

open Finset

namespace TaoTrudgianYang2025

theorem finite_moment_large_value_count {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (V : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hV : 0 < V)
    (hmean : ∑ i ∈ s, f i = (s.card:ℝ)*V)
    (hsecond : ∑ i ∈ s, (f i)^2 ≤ 3*(s.card:ℝ)*V^2) :
    (s.card:ℝ) ≤ 12*({i ∈ s | V/2 ≤ f i}.card:ℝ) := by
  classical
  let g := {i ∈ s | V/2 ≤ f i}
  let b := {i ∈ s | ¬ V/2 ≤ f i}
  have hsplit : (∑ i ∈ g, f i)+(∑ i ∈ b, f i) = ∑ i ∈ s, f i :=
    sum_filter_add_sum_filter_not s (fun i => V/2 ≤ f i) f
  have hb : ∑ i ∈ b, f i ≤ (s.card:ℝ)*(V/2) := by
    calc
      _ ≤ ∑ _i ∈ b, V/2 := sum_le_sum (fun i hi =>
        (lt_of_not_ge (mem_filter.mp hi).2).le)
      _ = (b.card:ℝ)*(V/2) := by simp
      _ ≤ (s.card:ℝ)*(V/2) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_le_card (filter_subset _ _)) (by positivity)
  have hlo : (s.card:ℝ)*V ≤ 2*(∑ i ∈ g, f i) := by linarith
  have hsum : 0 ≤ ∑ i ∈ g, f i :=
    sum_nonneg (fun i hi => hf i ((filter_subset _ _) hi))
  have hsq := sq_sum_le_card_mul_sum_sq (s:=g) (f:=f)
  have hmoment : ∑ i ∈ g, (f i)^2 ≤ 3*(s.card:ℝ)*V^2 :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun i _ _ => sq_nonneg (f i))).trans hsecond
  have hg0 : (0:ℝ) ≤ g.card := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_left hmoment hg0
  by_cases hs : s.card = 0
  · simp only [hs,Nat.cast_zero]
    positivity
  have hc : (0:ℝ) < s.card := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  have hcV : 0 < (s.card:ℝ)*V^2 := mul_pos hc (sq_pos_of_pos hV)
  apply le_of_mul_le_mul_right (a:=(s.card:ℝ)*V^2) _ hcV
  have hlowSq : ((s.card:ℝ)*V)^2 ≤ (2*(∑ i ∈ g, f i))^2 :=
    pow_le_pow_left₀ (mul_nonneg hc.le hV.le) hlo 2
  nlinarith

end TaoTrudgianYang2025

