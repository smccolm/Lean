import GafniTao.FordLemma65Scale
import GafniTao.FordMomentReal
import Mathlib.Data.Nat.Choose.Cast

/-!
# Ford Lemma 6.5: exact exponent ledger

This is the algebra behind the one-step update `Delta' = (1-1/k) Delta`.
The selected-prime exponent is kept as a natural number until its exact cast
is identified with Ford's triangular-number expression.
-/

namespace GafniTao

noncomputable section

def fordLemma65PrimeExponent (s k : ℕ) : ℕ :=
  2 * s + k.choose 2

def fordDelta65 (k : ℕ) (delta : ℝ) : ℝ :=
  delta * (1 - 1 / (k : ℝ))

def fordLemma65Coefficient (s k : ℕ) (C : ℝ) : ℝ :=
  4 * (k : ℝ) ^ 3 * k.factorial *
    (2 : ℝ) ^ fordLemma65PrimeExponent s k * C

theorem fordLemma65_source_exponent_eq (s k : ℕ) :
    2 * s + (k - 1) * k / 2 = fordLemma65PrimeExponent s k := by
  simp [fordLemma65PrimeExponent, Nat.choose_two_right, mul_comm]

theorem fordLemma65PrimeExponent_cast
    (s k : ℕ) :
    (fordLemma65PrimeExponent s k : ℝ) =
      2 * (s : ℝ) + ((k : ℝ) ^ 2 - k) / 2 := by
  rw [fordLemma65PrimeExponent, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_choose_two]
  ring

/-- The complete exponent cancellation in Ford's Lemma 6.5. -/
theorem fordLemma65_exponent_identity
    (s k : ℕ) (delta : ℝ) (hk : 1 ≤ k) :
    (fordLemma65PrimeExponent s k : ℝ) / k + k +
        fordLambda34 s k delta * (1 - 1 / (k : ℝ)) =
      fordLambda34 (s + k) k (fordDelta65 k delta) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [fordLemma65PrimeExponent_cast s k]
  unfold fordLambda34 fordDelta65
  push_cast
  field_simp [hkR]
  ring

theorem fordLemma65_scale_prime_power_identity
    {s k : ℕ} {Q : ℝ} (hk : 1 ≤ k) (hQ : 0 < Q) :
    fordLemma65Scale k Q ^ fordLemma65PrimeExponent s k =
      Q ^ ((fordLemma65PrimeExponent s k : ℝ) / k) := by
  rw [← Real.rpow_natCast, fordLemma65Scale, ← Real.rpow_mul hQ.le]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  congr 1
  field_simp [hkR]

theorem fordLemma65_power_identity
    {s k : ℕ} {delta Q : ℝ}
    (hk : 1 ≤ k) (hQ : 0 < Q) :
    fordLemma65Scale k Q ^ fordLemma65PrimeExponent s k * Q ^ k *
        (Q ^ (1 - 1 / (k : ℝ))) ^ fordLambda34 s k delta =
      Q ^ fordLambda34 (s + k) k (fordDelta65 k delta) := by
  rw [fordLemma65_scale_prime_power_identity hk hQ,
    ← Real.rpow_natCast, ← Real.rpow_mul hQ.le,
    ← Real.rpow_add hQ, ← Real.rpow_add hQ]
  congr 1
  simpa [mul_comm] using fordLemma65_exponent_identity s k delta hk

theorem fordLemma65_selected_power_bound
    {s k p : ℕ} {Q : ℝ}
    (hp : (p : ℝ) ≤ 2 * fordLemma65Scale k Q) :
    ((p ^ fordLemma65PrimeExponent s k : ℕ) : ℝ) ≤
      (2 : ℝ) ^ fordLemma65PrimeExponent s k *
        fordLemma65Scale k Q ^ fordLemma65PrimeExponent s k := by
  rw [Nat.cast_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hp _

#print axioms fordLemma65_source_exponent_eq
#print axioms fordLemma65PrimeExponent_cast
#print axioms fordLemma65_exponent_identity
#print axioms fordLemma65_scale_prime_power_identity
#print axioms fordLemma65_power_identity
#print axioms fordLemma65_selected_power_bound

end

end GafniTao
