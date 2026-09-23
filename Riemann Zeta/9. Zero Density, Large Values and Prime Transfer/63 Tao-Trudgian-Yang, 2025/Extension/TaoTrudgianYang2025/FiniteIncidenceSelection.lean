import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Finite double counting selects one common sample for many ordinates. -/

open Finset

namespace TaoTrudgianYang2025

theorem finite_incidence_exists_row {ι κ : Type*}
    (s : Finset ι) (w : Finset κ) (R : ι → κ → Prop) [DecidableRel R]
    (K : ℝ) (hs : s.Nonempty)
    (hcol : ∀ t ∈ w, (s.card:ℝ) ≤ K*({i ∈ s | R i t}.card:ℝ)) :
    ∃ i ∈ s, (w.card:ℝ) ≤ K*({t ∈ w | R i t}.card:ℝ) := by
  have hswapNat : ∑ t ∈ w, ({i ∈ s | R i t}.card) =
      ∑ i ∈ s, ({t ∈ w | R i t}.card) := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  have hswap : ∑ t ∈ w, ({i ∈ s | R i t}.card:ℝ) =
      ∑ i ∈ s, ({t ∈ w | R i t}.card:ℝ) := by exact_mod_cast hswapNat
  apply exists_le_of_sum_le hs
  calc
    ∑ _i ∈ s, (w.card:ℝ) = (w.card:ℝ)*(s.card:ℝ) := by simp [mul_comm]
    _ = ∑ _t ∈ w, (s.card:ℝ) := by simp
    _ ≤ ∑ t ∈ w, K*({i ∈ s | R i t}.card:ℝ) := sum_le_sum hcol
    _ = ∑ i ∈ s, K*({t ∈ w | R i t}.card:ℝ) := by
      rw [← mul_sum,hswap,mul_sum]

end TaoTrudgianYang2025

