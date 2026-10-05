import DhimanKadiriQuesadaHerrera2026.Objects
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

/-!
# Kernel regressions for discrepancies in arXiv:2609.00537v1

These prove exact source diagnostics, not the paper's analytic error bounds.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators

/-- E01: the inclusive sharp sum and the printed sum differ by exactly one. -/
theorem sharpZetaSum_eq_one_add_printed (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    sharpZetaSum s x = 1 + printedAFE1Sum s x := by
  have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by simpa using hx)
  have hset : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Ioc 1 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  simp [sharpZetaSum, printedAFE1Sum, hset, zetaTerm]

/-- E01: the discrepancy has norm one for every complex exponent. -/
theorem norm_sharpZetaSum_sub_printed (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖sharpZetaSum s x - printedAFE1Sum s x‖ = 1 := by
  rw [sharpZetaSum_eq_one_add_printed s hx]
  simp

/-- E01: both residuals cannot satisfy bounds whose sum is less than one. -/
theorem one_le_sum_of_afe1_residual_bounds (s : ℂ) {x a b : ℝ} (hx : 1 ≤ x)
    (ha : ‖riemannZeta s - sharpZetaSum s x‖ ≤ a)
    (hb : ‖riemannZeta s - printedAFE1Sum s x‖ ≤ b) : 1 ≤ a + b := by
  have htri := norm_sub_le (riemannZeta s - printedAFE1Sum s x)
    (riemannZeta s - sharpZetaSum s x)
  have hid : (riemannZeta s - printedAFE1Sum s x) -
      (riemannZeta s - sharpZetaSum s x) = sharpZetaSum s x - printedAFE1Sum s x := by
    ring
  rw [hid, norm_sharpZetaSum_sub_printed s hx] at htri
  linarith

/-- E02: the displayed universal functional equation in section 2.5 fails at -2. -/
theorem printed_functional_equation_fails_at_neg_two :
    riemannZeta (1 - (-2 : ℂ)) ≠ chi (-2) * riemannZeta (-2) := by
  have hzero : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  rw [hzero, mul_zero]
  apply riemannZeta_ne_zero_of_one_le_re
  norm_num

/-- E02: the literal universal sentence cannot be an accepted public contract. -/
theorem not_printed_functional_equation :
    ¬ ∀ s : ℂ, riemannZeta (1 - s) = chi s * riemannZeta s := by
  intro h
  exact printed_functional_equation_fails_at_neg_two (h (-2))

end DhimanKadiriQuesadaHerrera2026
