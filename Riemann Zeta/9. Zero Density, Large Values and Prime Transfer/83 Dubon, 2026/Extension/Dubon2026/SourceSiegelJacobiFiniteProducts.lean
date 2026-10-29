import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary existence -> literal Siegel-product
holomorphy and SL2 transformation -> Jacobi theta product identity. The
finite Gaussian identity is the source finite approximation needed to
identify the actual product with Mathlib's analytic theta function.
Native q-series multiplication and cusp limits are already proved and
will be reused. No abstract q-series generalization is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
noncomputable section
open Finset

/-- The finite Euler product in the source Gaussian identity. -/
def qfact (Q : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - Q ^ (i + 1))

/-- The actual Gaussian quotient of finite Euler products. -/
def qbinom (Q : ℂ) (m k : ℕ) : ℂ :=
  if k ≤ m then qfact Q m / (qfact Q k * qfact Q (m - k)) else 0

theorem qfact_zero (Q : ℂ) : qfact Q 0 = 1 := by
  unfold qfact
  exact Finset.prod_range_zero _

theorem qfact_succ (Q : ℂ) (m : ℕ) : qfact Q (m + 1) = qfact Q m * (1 - Q ^ (m + 1)) := by
  unfold qfact
  exact Finset.prod_range_succ _ m

theorem one_sub_pow_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (i : ℕ) : 1 - Q ^ (i + 1) ≠ 0 := by
  intro h
  have h1 : Q ^ (i + 1) = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have h2 : ‖Q ^ (i + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hQ (Nat.succ_ne_zero i)
  rw [h1, norm_one] at h2
  exact lt_irrefl 1 h2

theorem qfact_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : qfact Q m ≠ 0 := by
  unfold qfact
  rw [Finset.prod_ne_zero_iff]
  exact fun i _ => one_sub_pow_ne_zero hQ i

theorem qbinom_zero_right {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : qbinom Q m 0 = 1 := by
  unfold qbinom
  rw [if_pos (Nat.zero_le m), qfact_zero, one_mul, Nat.sub_zero,
    div_self (qfact_ne_zero hQ m)]

theorem qbinom_self {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : qbinom Q m m = 1 := by
  unfold qbinom
  rw [if_pos le_rfl, Nat.sub_self, qfact_zero, mul_one, div_self (qfact_ne_zero hQ m)]

theorem qbinom_of_gt (Q : ℂ) {m k : ℕ} (h : m < k) : qbinom Q m k = 0 := by
  unfold qbinom
  rw [if_neg (not_le.mpr h)]

theorem qbinom_succ_succ {Q : ℂ} (hQ : ‖Q‖ < 1) (m k : ℕ) :
    qbinom Q (m + 1) (k + 1) = qbinom Q m (k + 1) + Q ^ (m - k) * qbinom Q m k := by
  rcases lt_trichotomy k m with hkm | rfl | hkm
  ·
    have hk1m : k + 1 ≤ m := hkm
    unfold qbinom
    rw [if_pos (by omega : k + 1 ≤ m + 1), if_pos hk1m, if_pos (by omega : k ≤ m)]
    have e1 : m + 1 - (k + 1) = m - k := by omega
    have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e1, qfact_succ Q m, e2, qfact_succ Q (m - (k + 1))]
    have hf1 : qfact Q (k + 1) ≠ 0 := qfact_ne_zero hQ _
    have hf2 : qfact Q (m - (k + 1)) ≠ 0 := qfact_ne_zero hQ _
    have hf3 : qfact Q k ≠ 0 := qfact_ne_zero hQ _
    have hone : (1 : ℂ) - Q ^ (m - (k + 1) + 1) ≠ 0 := one_sub_pow_ne_zero hQ _
    rw [qfact_succ Q k]
    have hone2 : (1 : ℂ) - Q ^ (k + 1) ≠ 0 := one_sub_pow_ne_zero hQ _
    field_simp
    ring_nf
    have hpow : Q ^ 2 * Q ^ k * Q ^ (m - (1 + k)) = Q * Q ^ m := by
      calc Q ^ 2 * Q ^ k * Q ^ (m - (1 + k)) = Q ^ (2 + k + (m - (1 + k))) := by
            rw [← pow_add, ← pow_add]
        _ = Q ^ (1 + m) := by
            congr 1
            omega
        _ = Q * Q ^ m := by
            rw [pow_add, pow_one]
    linear_combination qfact Q m * hpow
  ·
    rw [qbinom_self hQ, qbinom_of_gt Q (Nat.lt_succ_self k), qbinom_self hQ,
      Nat.sub_self, pow_zero, zero_add, one_mul]
  ·
    rw [qbinom_of_gt Q (by omega : m < k + 1), qbinom_of_gt Q (by omega : m + 1 < k + 1),
      qbinom_of_gt Q hkm, mul_zero, add_zero]


end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct
