import Dubon2026.PrimitiveFullCoefficients
import Dubon2026.PrimitiveCoefficientReality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! # Actual normalized primitive coefficients and symmetric-power polynomials

The Hecke recurrence is derived from the actual operators and q-expansion.
No Ramanujan bound or arithmetic equidistribution is assumed or concluded.
-/

namespace Dubon2026

open Polynomial

noncomputable section

/-- Positive-natural principal powers preserve the genuine prime-power normalization. -/
theorem nat_power_cpow_real (p r : ℕ) (c : ℝ) :
    ((p ^ r : ℕ) : ℂ) ^ (c : ℂ) = ((p : ℂ) ^ (c : ℂ)) ^ r := by
  push_cast
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- The actual normalized primitive coefficients are multiplicative at every coprime pair. -/
theorem primitiveCuspForm_normalized_mul {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (n m : ℕ) (hnm : n.Coprime m) :
    normalizedCuspCoefficients f.toCuspForm (n * m) =
      normalizedCuspCoefficients f.toCuspForm n * normalizedCuspCoefficients f.toCuspForm m := by
  simp only [normalizedCuspCoefficients, shiftedCoefficients,
    primitiveCuspForm_coefficient_mul_all f n m hnm, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

/-- At an unramified prime, the genuine normalization changes the Hecke recurrence to determinant one. -/
theorem primitiveCuspForm_normalized_primePower_recurrence {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    normalizedCuspCoefficients f.toCuspForm (p ^ (r + 2)) =
      normalizedCuspCoefficients f.toCuspForm p *
        normalizedCuspCoefficients f.toCuspForm (p ^ (r + 1)) -
          normalizedCuspCoefficients f.toCuspForm (p ^ r) := by
  let c : ℝ := -((k : ℝ) - 1) / 2
  let u : ℂ := (p : ℂ) ^ (c : ℂ)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hweight : heckeDivisorWeight Q k p * u ^ 2 = 1 := by
    change (if Nat.Coprime p Q then (p : ℂ) ^ (k - 1) else 0) * u ^ 2 = 1
    rw [if_pos (hp.coprime_iff_not_dvd.mpr hpQ)]
    dsimp only [u]
    rw [← Complex.cpow_intCast, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hp0]
    have he : (((k - 1 : ℤ) : ℂ) + (2 : ℕ) * (c : ℂ)) = 0 := by
      dsimp only [c]
      push_cast
      ring
    rw [he, Complex.cpow_zero]
  have hs (j : ℕ) : normalizedCuspCoefficients f.toCuspForm (p ^ j) =
      cuspCoefficients f.toCuspForm (p ^ j) * u ^ j := by
    exact congrArg (cuspCoefficients f.toCuspForm (p ^ j) * ·) (nat_power_cpow_real p j c)
  rw [hs, hs, hs, primitiveCuspForm_primePower_recurrence f hp]
  change (cuspCoefficients f.toCuspForm p * cuspCoefficients f.toCuspForm (p ^ (r + 1)) -
      heckeDivisorWeight Q k p * cuspCoefficients f.toCuspForm (p ^ r)) * u ^ (r + 2) =
    (cuspCoefficients f.toCuspForm p * u) *
      (cuspCoefficients f.toCuspForm (p ^ (r + 1)) * u ^ (r + 1)) -
        cuspCoefficients f.toCuspForm (p ^ r) * u ^ r
  rw [pow_add, pow_succ]
  linear_combination -cuspCoefficients f.toCuspForm (p ^ r) * u ^ r * hweight

/-- Every actual normalized good prime-power coefficient is the symmetric-power character polynomial in its prime coefficient. -/
theorem primitiveCuspForm_normalized_primePower_chebyshev {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    normalizedCuspCoefficients f.toCuspForm (p ^ r) =
      (Chebyshev.S ℂ (r : ℤ)).eval (normalizedCuspCoefficients f.toCuspForm p) := by
  induction r using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, Nat.cast_zero, Chebyshev.S_zero, eval_one] using
      normalizedCuspCoefficients_one f.toCuspForm f.normalized
  | one => simp only [pow_one, Nat.cast_one, Chebyshev.S_one, eval_X]
  | more r ih0 ih1 =>
    rw [primitiveCuspForm_normalized_primePower_recurrence f hp hpQ, ih0, ih1]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Chebyshev.S_add_two, eval_sub, eval_mul, eval_X]

/-- The same exact prime-power identity in the real normalization proved by Hecke adjointness. -/
theorem primitiveCuspForm_normalized_primePower_re {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (r : ℕ) :
    (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re =
      (Chebyshev.S ℝ (r : ℤ)).eval (normalizedCuspCoefficients f.toCuspForm p).re := by
  have hz : normalizedCuspCoefficients f.toCuspForm p =
      ((normalizedCuspCoefficients f.toCuspForm p).re : ℂ) :=
    Complex.ext rfl (by simpa using (primitiveCuspForm_normalizedCoefficient_im f p
      (hp.coprime_iff_not_dvd.mpr hpQ)))
  rw [primitiveCuspForm_normalized_primePower_chebyshev f hp hpQ, hz,
    ← Chebyshev.complex_ofReal_eval_S, Complex.ofReal_re]
  rw [Complex.ofReal_re]

end
end Dubon2026
