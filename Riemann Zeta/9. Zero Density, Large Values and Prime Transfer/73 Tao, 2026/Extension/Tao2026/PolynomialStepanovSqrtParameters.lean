import Tao2026.BurgessWeilPrimeKummerWeilAmplification
import Tao2026.PolynomialStepanovSimpleRoot

/-!
# Explicit square-root parameters for Stepanov point counts

A natural floor of a scaled square root meets the strict dimension condition.
The resulting estimate has an explicit constant depending only on the fiber
index and polynomial degree, independent of the extension field size.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem nat_stepanov_exists_sqrt_parameters
    (e d h Q : ℕ) (he : 0 < e) (hh : 2 ≤ h) (hround : Q ≤ e * (h + 1))
    (hlarge : 16 * e ^ 2 * (e * d + 1) ^ 2 ≤ Q) :
    ∃ k : ℕ, 0 < k ∧ k ^ 2 * (e * d + 1) < h ∧
      Real.sqrt Q ≤ 4 * (e : ℝ) * (e * d + 1) * k := by
  let A : ℝ := (e : ℝ) * d + 1
  let D : ℝ := 2 * e * A
  let R : ℝ := Real.sqrt Q
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hA : 1 ≤ A := by dsimp [A]; linarith [mul_nonneg (Nat.cast_nonneg e : (0 : ℝ) ≤ e) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = Q := Real.sq_sqrt (Nat.cast_nonneg Q)
  have hlarge' : (2 * D) ^ 2 ≤ (Q : ℝ) := by
    have hl : (16 : ℝ) * (e : ℝ) ^ 2 * ((e : ℝ) * d + 1) ^ 2 ≤ Q := by exact_mod_cast hlarge
    dsimp [D, A]
    nlinarith only [hl]
  have hRlarge : 2 * D ≤ R := by nlinarith
  let k : ℕ := ⌊R / D⌋₊
  have hkUpper : (k : ℝ) * D ≤ R := by
    exact (le_div_iff₀ hD).1 (Nat.floor_le (div_nonneg hR hD.le))
  have hkLower : R < ((k : ℝ) + 1) * D := by
    exact (div_lt_iff₀ hD).1 (Nat.lt_floor_add_one (R / D))
  have hkSqrt : R ≤ 2 * D * k := by nlinarith
  have hkpos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := by omega
    rw [hkz, Nat.cast_zero, mul_zero] at hkSqrt
    linarith
  have hkSq : (k : ℝ) ^ 2 * D ^ 2 ≤ Q := by
    nlinarith [sq_nonneg (R - k * D)]
  have hround' : (Q : ℝ) ≤ (e : ℝ) * (h + 1) := by exact_mod_cast hround
  have hsmallReal : (k : ℝ) ^ 2 * A < (h : ℝ) := by
    have hh' : (2 : ℝ) ≤ h := by exact_mod_cast hh
    have hDD : D ≤ D ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hDD (sq_nonneg (k : ℝ))
    dsimp [D] at hmul
    nlinarith
  refine ⟨k, hkpos, ?_, ?_⟩
  · dsimp [A] at hsmallReal
    exact_mod_cast hsmallReal
  · change R ≤ _
    dsimp [D, A] at hkSqrt
    nlinarith only [hkSqrt]

theorem nat_stepanov_count_le_sqrt_of_parameters
    (N e d h Q k : ℕ) (he : 0 < e) (hk : 0 < k) (hQ : e * h ≤ Q)
    (hcount : N * (e * k) ≤ h - 1 + h * (e - 1) * d + Q * k)
    (hsqrt : Real.sqrt Q ≤ 4 * (e : ℝ) * (e * d + 1) * k) :
    (N : ℝ) * e ≤ Q + 4 * (e : ℝ) * (e * d + 1) ^ 2 * Real.sqrt Q := by
  have hhQ : h ≤ Q := (Nat.le_mul_of_pos_left h he).trans hQ
  have hrem : h - 1 + h * (e - 1) * d ≤ Q * (e * d + 1) := by
    calc
      _ ≤ h + h * e * d := by gcongr <;> omega
      _ ≤ Q + Q * e * d := by gcongr
      _ = _ := by ring
  have hcount' : (N : ℝ) * (e * k) ≤ Q * ((e : ℝ) * d + 1) + Q * k := by
    exact_mod_cast hcount.trans (Nat.add_le_add_right hrem (Q * k))
  have hs := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (Q : ℝ))
  rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg Q)] at hs
  have hA : 0 ≤ (e : ℝ) * d + 1 := by positivity
  have hsA := mul_le_mul_of_nonneg_right hs hA
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  nlinarith only [hcount', hsA, hk']

theorem polynomialStepanov_card_le_sqrt_of_simple_root
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (e h n : ℕ) (c : K) (he : 0 < e) (hh : 2 ≤ h)
    (hQ : e * h ≤ p ^ n) (hround : p ^ n ≤ e * (h + 1))
    (hlarge : 16 * e ^ 2 * (e * g.natDegree + 1) ^ 2 ≤ p ^ n)
    (T : Finset K) (hT : ∀ x ∈ T, x ^ p ^ n = x ∧ g.eval x ≠ 0 ∧ g.eval x ^ h = c) :
    (T.card : ℝ) * e ≤ p ^ n + 4 * (e : ℝ) * (e * g.natDegree + 1) ^ 2 * Real.sqrt (p ^ n) := by
  obtain ⟨k, hk, hdim, hsqrt⟩ := nat_stepanov_exists_sqrt_parameters e g.natDegree h (p ^ n)
    he hh hround hlarge
  have hcount := polynomialStepanov_card_mul_le_simple_parameters p g hg hroot e h n k c he hQ hdim T hT
  simpa only [Nat.cast_pow] using nat_stepanov_count_le_sqrt_of_parameters T.card e g.natDegree h
    (p ^ n) k he hk hQ hcount hsqrt

end
end Tao2026
