import GafniTao.FordVinogradovMomentMonotone
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Ford Lemma 6.3: the pointwise `S₀` moment ledger

This is the finite Hölder estimate preceding Ford's integration over the
phase boxes.  The coefficient is deliberately left in its exact pre-
simplification form; the following integration lemma will turn it into the
source factor `2^(4s)`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLemma63_tail_coefficient_le
    {M r : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    (2 / (M : ℝ)) ^ r * ((M - 1 : ℕ) : ℝ) ^ (r - 1) ≤
      (2 : ℝ) ^ r / M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : (((M - 1 : ℕ) : ℝ)) ≤ M := by exact_mod_cast Nat.sub_le M 1
  have hpow : (((M : ℝ) ^ (r - 1)) * M) = (M : ℝ) ^ r := by
    rw [← pow_succ, Nat.sub_add_cancel hr]
  calc
    (2 / (M : ℝ)) ^ r * ((M - 1 : ℕ) : ℝ) ^ (r - 1) ≤
        (2 / (M : ℝ)) ^ r * (M : ℝ) ^ (r - 1) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsub (r - 1)) (pow_nonneg (by positivity) r)
    _ = (2 : ℝ) ^ r / M := by
      rw [div_pow]
      field_simp [hMpos.ne']
      exact hpow

theorem fordLemma63SZero_power_prebound
    {k M r : ℕ} {β : Fin k → ℝ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    fordLemma63SZero k M β ^ r ≤
      2 ^ (r - 1) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (2 / (M : ℝ)) ^ r * ((M - 1 : ℕ) : ℝ) ^ (r - 1) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
  let A : ℝ := ‖fordLemma63PolynomialSum k M β‖
  let C : ℝ := ∑ q ∈ Finset.range (M - 1),
    ‖fordLemma63PolynomialSum k (q + 1) β‖
  let D : ℝ := ∑ q ∈ Finset.range (M - 1),
    ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r
  have hA : 0 ≤ A := norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hcoef : 0 ≤ (2 / (M : ℝ)) := by positivity
  have hholder : C ^ r ≤ ((M - 1 : ℕ) : ℝ) ^ (r - 1) * D := by
    dsimp [C, D]
    have h := pow_sum_le_card_mul_sum_pow
      (s := Finset.range (M - 1))
      (f := fun q => ‖fordLemma63PolynomialSum k (q + 1) β‖)
      (fun q hq => norm_nonneg (fordLemma63PolynomialSum k (q + 1) β))
      (r - 1)
    rw [Nat.sub_add_cancel hr] at h
    simpa using h
  have htail : fordLemma63SZeroTail k M β ^ r ≤
      (2 / (M : ℝ)) ^ r * ((M - 1 : ℕ) : ℝ) ^ (r - 1) * D := by
    unfold fordLemma63SZeroTail
    rw [mul_pow]
    simpa only [C, D, mul_assoc] using
      (mul_le_mul_of_nonneg_left hholder (pow_nonneg hcoef r))
  have htailNonneg : 0 ≤ fordLemma63SZeroTail k M β := by
    unfold fordLemma63SZeroTail
    positivity
  have hadd := add_pow_le hA htailNonneg r
  change (A + fordLemma63SZeroTail k M β) ^ r ≤
    2 ^ (r - 1) *
      (A ^ r + (2 / (M : ℝ)) ^ r *
        ((M - 1 : ℕ) : ℝ) ^ (r - 1) * D)
  calc
    (A + fordLemma63SZeroTail k M β) ^ r ≤
        2 ^ (r - 1) * (A ^ r + fordLemma63SZeroTail k M β ^ r) := hadd
    _ ≤ 2 ^ (r - 1) *
        (A ^ r + (2 / (M : ℝ)) ^ r *
          ((M - 1 : ℕ) : ℝ) ^ (r - 1) * D) := by
      gcongr
    _ = _ := rfl

/-- Ford's simplified pointwise ledger.  At `r = 2s` its constant is the
source `2^(4s)`. -/
theorem fordLemma63SZero_power_le
    {k M r : ℕ} {β : Fin k → ℝ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    fordLemma63SZero k M β ^ r ≤
      (2 : ℝ) ^ (2 * r) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
  let A : ℝ := ‖fordLemma63PolynomialSum k M β‖ ^ r
  let D : ℝ := ∑ q ∈ Finset.range (M - 1),
    ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r
  let c : ℝ := (2 : ℝ) ^ (r - 1)
  let B : ℝ := (2 : ℝ) ^ r
  let C : ℝ := (2 : ℝ) ^ (2 * r)
  have hpre := fordLemma63SZero_power_prebound (k := k) (M := M) (r := r) (β := β) hM hr
  have hcoef := fordLemma63_tail_coefficient_le (M := M) (r := r) hM hr
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hY : 0 ≤ (1 / (M : ℝ)) * D := mul_nonneg (by positivity) hD
  have hcC : c ≤ C := by
    dsimp [c, C]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hcBC : c * B ≤ C := by
    dsimp [c, B, C]
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    fordLemma63SZero k M β ^ r ≤
        c * (A +
          ((2 / (M : ℝ)) ^ r * ((M - 1 : ℕ) : ℝ) ^ (r - 1)) * D) := by
      simpa only [A, D, c, mul_assoc] using hpre
    _ ≤ c * (A + (B / (M : ℝ)) * D) := by
      gcongr
    _ = c * A + (c * B) * ((1 / (M : ℝ)) * D) := by
      field_simp [hMpos.ne']
    _ ≤ C * A + C * ((1 / (M : ℝ)) * D) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hcC hA)
        (mul_le_mul_of_nonneg_right hcBC hY)
    _ = C * (A + (1 / (M : ℝ)) * D) := by ring
    _ = _ := rfl

/-- The asymmetric form used under the integral; retaining the coefficient
of the complete sum is what yields Ford's exact `2^(4s)` rather than an
extraneous factor two. -/
theorem fordLemma63SZero_power_le_sharp
    {k M r : ℕ} {β : Fin k → ℝ} (hM : 1 ≤ M) (hr : 1 ≤ r) :
    fordLemma63SZero k M β ^ r ≤
      (2 : ℝ) ^ (r - 1) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          (2 : ℝ) ^ r * (1 / (M : ℝ)) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
  have hpre := fordLemma63SZero_power_prebound
    (k := k) (M := M) (r := r) (β := β) hM hr
  have hcoef := fordLemma63_tail_coefficient_le (M := M) (r := r) hM hr
  have hD : 0 ≤ ∑ q ∈ Finset.range (M - 1),
      ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r := by positivity
  calc
    fordLemma63SZero k M β ^ r ≤
        (2 : ℝ) ^ (r - 1) *
          (‖fordLemma63PolynomialSum k M β‖ ^ r +
            ((2 / (M : ℝ)) ^ r * ((M - 1 : ℕ) : ℝ) ^ (r - 1)) *
              ∑ q ∈ Finset.range (M - 1),
                ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
      simpa only [mul_assoc] using hpre
    _ ≤ (2 : ℝ) ^ (r - 1) *
        (‖fordLemma63PolynomialSum k M β‖ ^ r +
          ((2 : ℝ) ^ r / M) *
            ∑ q ∈ Finset.range (M - 1),
              ‖fordLemma63PolynomialSum k (q + 1) β‖ ^ r) := by
      gcongr
    _ = _ := by ring

#print axioms fordLemma63SZero_power_prebound
#print axioms fordLemma63_tail_coefficient_le
#print axioms fordLemma63SZero_power_le
#print axioms fordLemma63SZero_power_le_sharp

end

end GafniTao
