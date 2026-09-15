import Tao2026.ErdosSelfridgeFiniteSeventy
import Tao2026.ErdosSelfridgePrimorial

/-!
# Explicit growth after Erdős--Selfridge equation (23)

This file replaces the asymptotic exponential-dominance step by the paper's
explicit cutoff.  Rational lower bounds for the two fractional powers give
`31335 / 10000` as a strict lower bound for the effective base.  A direct
base calculation at `H = 297`, followed by an elementary ratio induction,
then proves that the equation-(23) left side dominates the polynomially
weighted `3^H` bound for every `H >= 297`.
-/

namespace Tao2026

set_option exponentiation.threshold 512

private theorem one_five_eight_seven_four_lt_two_rpow_two_thirds :
    (15874 / 10000 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  calc
    (15874 / 10000 : ℝ) < (4 : ℝ) ^ ((3 : ℝ)⁻¹) := by
      rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    _ = (2 : ℝ) ^ (2 / 3 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num)]
      congr 1

private theorem one_three_one_six_lt_three_rpow_one_quarter :
    (1316 / 1000 : ℝ) < (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
  rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- A rational lower bound, sharp enough to recover the paper's cutoff 297,
for the effective exponential base in equation (23). -/
theorem equation23Base_rational_lower :
    (31335 / 10000 : ℝ) < erdosSelfridgeEquation23Base := by
  dsimp [erdosSelfridgeEquation23Base]
  calc
    (31335 / 10000 : ℝ) <
        (3 / 2 : ℝ) * (15874 / 10000) * (1316 / 1000) := by norm_num
    _ < (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) * (1316 / 1000) := by
      gcongr
      exact one_five_eight_seven_four_lt_two_rpow_two_thirds
    _ < (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) *
        (3 : ℝ) ^ (1 / 4 : ℝ) := by
      gcongr
      exact one_three_one_six_lt_three_rpow_one_quarter

/-- The exact rational comparison underlying the cutoff `H = 297`. -/
theorem equation23_three_pow_lt_rational_pow_of_297_le
    {H : ℕ} (hH : 297 ≤ H) :
    (14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H <
      (31335 / 10000 : ℝ) ^ H := by
  induction H, hH using Nat.le_induction with
  | base =>
      norm_num [div_pow]
  | succ H hH ih =>
      have hHreal : (297 : ℝ) ≤ H := by exact_mod_cast hH
      have hratio :
          (3 : ℝ) * ((H + 1 : ℕ) : ℝ) ^ 2 ≤
            (31335 / 10000 : ℝ) * (H : ℝ) ^ 2 := by
        norm_num at ⊢
        nlinarith [sq_nonneg ((H : ℝ) - 297)]
      calc
        (14 / 3 : ℝ) * ((H + 1 : ℕ) : ℝ) ^ 2 * (3 : ℝ) ^ (H + 1) =
            (14 / 3 : ℝ) *
              ((3 : ℝ) * ((H + 1 : ℕ) : ℝ) ^ 2) * (3 : ℝ) ^ H := by
                rw [pow_succ]
                ring
        _ ≤ (14 / 3 : ℝ) *
              ((31335 / 10000 : ℝ) * (H : ℝ) ^ 2) * (3 : ℝ) ^ H := by
                gcongr
        _ = ((14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H) *
              (31335 / 10000 : ℝ) := by ring
        _ < (31335 / 10000 : ℝ) ^ H * (31335 / 10000 : ℝ) := by
              exact mul_lt_mul_of_pos_right ih (by norm_num)
        _ = (31335 / 10000 : ℝ) ^ (H + 1) := by rw [pow_succ]

/-- The explicit exponential-dominance half of the paper's large-length
argument.  It is independent of any primorial estimate. -/
theorem equation23_three_pow_lt_left_of_297_le
    {H : ℕ} (hH : 297 ≤ H) :
    (14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H <
      erdosSelfridgeEquation23Base ^ H := by
  refine (equation23_three_pow_lt_rational_pow_of_297_le hH).trans ?_
  exact pow_lt_pow_left₀ equation23Base_rational_lower (by norm_num) (by omega)

set_option maxRecDepth 100000 in
/-- Closed arithmetic certificate for the remaining source range
`71 <= H <= 296`, using the actual product of primes below `H`.  Clearing the
positive denominator `10000^H` leaves a proposition entirely in `ℕ`. -/
theorem equation23_finite_primeProduct_certificate
    {H : ℕ} (hHlower : 71 ≤ H) (hHupper : H ≤ 296) :
    14 * H ^ 2 * erdosSelfridgePrimeProduct H * 10000 ^ H <
      3 * 31335 ^ H := by
  interval_cases H <;> decide

/-- Real form of the closed arithmetic certificate. -/
theorem equation23_primeProduct_lt_rational_pow_of_71_le_of_le_296
    {H : ℕ} (hHlower : 71 ≤ H) (hHupper : H ≤ 296) :
    (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H <
      (31335 / 10000 : ℝ) ^ H := by
  rw [div_pow]
  calc
    (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H =
        ((14 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H) / 3 := by ring
    _ < (31335 : ℝ) ^ H / (10000 : ℝ) ^ H := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      have hcertificate :=
        equation23_finite_primeProduct_certificate hHlower hHupper
      have hcertificate' :
          14 * H ^ 2 * erdosSelfridgePrimeProduct H * 10000 ^ H <
            31335 ^ H * 3 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcertificate
      exact_mod_cast hcertificate'

/-- Equation (23) is numerically impossible throughout `71 <= H <= 296`. -/
theorem equation23_primeProduct_lt_left_of_71_le_of_le_296
    {H : ℕ} (hHlower : 71 ≤ H) (hHupper : H ≤ 296) :
    (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H <
      erdosSelfridgeEquation23Base ^ H := by
  refine (equation23_primeProduct_lt_rational_pow_of_71_le_of_le_296
    hHlower hHupper).trans ?_
  exact pow_lt_pow_left₀ equation23Base_rational_lower (by norm_num) (by omega)

/-- The complete finite part of Section 3.1, including the paper's exact
lower cutoff `H = 71`. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_71_le_of_le_296
    (hSS : SylvesterSchurConclusion) {N H : ℕ}
    (hHlower : 71 ≤ H) (hHupper : H ≤ 296) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  have heq23 := erdosSelfridge_equation23_of_failure
    hSS (by omega) hHN hfail
  rw [erdosSelfridge_equation23_left_eq_base_pow] at heq23
  have hreverse :=
    equation23_primeProduct_lt_left_of_71_le_of_le_296 hHlower hHupper
  exact lt_asymm heq23 hreverse

/-- Source-shaped hypothesis isolating the sole remaining arithmetic lemma:
the product of primes below `H` is bounded by `3^H`. -/
def ErdosSelfridgeThreePrimorialConclusion : Prop :=
  ∀ H : ℕ, erdosSelfridgePrimeProduct H ≤ 3 ^ H

/-- Above 296, the elementary `3^H` primorial bound and the explicit growth
lemma contradict equation (23). -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_297_le
    (hSS : SylvesterSchurConclusion)
    (hprime : ErdosSelfridgeThreePrimorialConclusion) {N H : ℕ}
    (hH : 297 ≤ H) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  intro hfail
  have heq23 := erdosSelfridge_equation23_of_failure
    hSS (by omega) hHN hfail
  rw [erdosSelfridge_equation23_left_eq_base_pow] at heq23
  have hprimeReal : (erdosSelfridgePrimeProduct H : ℝ) ≤ (3 : ℝ) ^ H := by
    exact_mod_cast hprime H
  have hrhs :
      (14 / 3 : ℝ) * (H : ℝ) ^ 2 * erdosSelfridgePrimeProduct H ≤
        (14 / 3 : ℝ) * (H : ℝ) ^ 2 * (3 : ℝ) ^ H := by
    gcongr
  have hgrowth := equation23_three_pow_lt_left_of_297_le hH
  exact (not_lt_of_ge ((heq23.trans_le hrhs).le)) hgrowth

/-- Exact Section 3.1 conclusion, conditional only on its named elementary
primorial input. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_71_le
    (hSS : SylvesterSchurConclusion)
    (hprime : ErdosSelfridgeThreePrimorialConclusion) {N H : ℕ}
    (hH : 71 ≤ H) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hsmall : H ≤ 296
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_71_le_of_le_296
      hSS hH hsmall hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_297_le
      hSS hprime (by omega) hHN

/-- The finite proof through 70 and the explicit Section 3.1 proof together
exclude every square-case prime-multiplicity failure. -/
theorem not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le
    (hSS : SylvesterSchurConclusion)
    (hprime : ErdosSelfridgeThreePrimorialConclusion) {N H : ℕ}
    (hH : 3 ≤ H) (hHN : H < N) :
    ¬ ErdosSelfridgePrimeMultiplicityFailureAt N H 2 := by
  by_cases hsmall : H ≤ 70
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le_of_le_seventy
      hSS hH hsmall hHN
  · exact not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_71_le
      hSS hprime (by omega) hHN

/-- The square specialization consumed by Tao's factorial-fiber argument,
conditional on Sylvester--Schur and the explicit elementary primorial bound. -/
theorem erdosSelfridgeSquareConclusion_of_sylvesterSchur_of_threePrimorial
    (hSS : SylvesterSchurConclusion)
    (hprime : ErdosSelfridgeThreePrimorialConclusion) :
    ErdosSelfridgeSquareConclusion := by
  apply erdosSelfridgeSquareConclusion_of_core
  intro N H hH hHN
  rintro ⟨r, hr⟩
  apply not_erdosSelfridgePrimeMultiplicityFailureAt_two_of_three_le
    hSS hprime hH hHN
  intro p _hpLower _hp
  rw [hr, Nat.factorization_pow]
  simp

end Tao2026
