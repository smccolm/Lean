import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Tactic

/-! DUB-17/18 -> regular-differential cusp decay -> bounded inverse-j
integral expression. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_coeffEmb_jq_inv.
The native Cauchy bound was checked; this finite-relation version directly
consumes the already proved relation without rebuilding a polynomial.
-/
namespace Dubon2026.SourceFunctionField
open scoped BigOperators

theorem norm_le_of_monic_relation {n : ℕ} {u : ℂ} {κ : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hκ : ∀ i ∈ Finset.range n, ‖κ i‖ ≤ B)
    (h : u ^ n + ∑ i ∈ Finset.range n, κ i * u ^ i = 0) : ‖u‖ ≤ n * B + 1 := by
  have hnB : 0 ≤ (n : ℝ) * B := mul_nonneg n.cast_nonneg hB
  by_cases hu' : ‖u‖ ≤ 1
  · linarith
  have hu : 1 < ‖u‖ := not_le.mp hu'
  have hn : n ≠ 0 := by rintro rfl; simp at h
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hun : u ^ (n' + 1) = -∑ i ∈ Finset.range (n' + 1), κ i * u ^ i :=
    eq_neg_of_add_eq_zero_left h
  have hle : ‖u‖ ^ (n' + 1) ≤ (n' + 1 : ℕ) * B * ‖u‖ ^ n' := by
    calc
      _ = ‖u ^ (n' + 1)‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range (n' + 1), κ i * u ^ i‖ := by rw [hun, norm_neg]
      _ ≤ ∑ i ∈ Finset.range (n' + 1), ‖κ i * u ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n' + 1), B * ‖u‖ ^ n' := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow]
        have hi' : i ≤ n' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact mul_le_mul (hκ i hi) (pow_le_pow_right₀ hu.le hi')
          (pow_nonneg (norm_nonneg _) _) hB
      _ = (n' + 1 : ℕ) * B * ‖u‖ ^ n' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hpos : 0 < ‖u‖ ^ n' := pow_pos (by linarith) _
  rw [pow_succ, mul_comm] at hle
  have := le_of_mul_le_mul_right hle hpos
  linarith

end Dubon2026.SourceFunctionField
