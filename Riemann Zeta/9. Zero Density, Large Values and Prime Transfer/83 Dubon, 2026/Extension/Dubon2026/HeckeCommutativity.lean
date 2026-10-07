import Dubon2026.HeckeAllIndices

/-! # Commutativity of the actual same-level cusp Hecke operators -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The index-zero finite Hecke sum is the zero cusp endomorphism. -/
theorem cuspHeckeLinear_zero (Q : ℕ) [NeZero Q] (k : ℤ) :
    cuspHeckeLinear Q k 0 = 0 := by
  apply LinearMap.ext
  intro f
  apply cuspCoefficients_injective Q k
  funext m
  change cuspCoefficients (cuspHecke 0 f) m = cuspCoefficientLinear Q k m 0
  rw [cuspHecke_coeff, map_zero]
  simp [classicalHeckeCoefficient]

/-- The index-one classical Hecke operator is the identity. -/
theorem cuspHeckeLinear_one (Q : ℕ) [NeZero Q] (k : ℤ) :
    cuspHeckeLinear Q k 1 = 1 := by
  simpa only [pow_zero, cuspHeckePrimePower] using
    cuspHeckeLinear_primePower Q k Nat.prime_two 0

/-- The actual cusp operators obey the prime-power recurrence at good and bad primes. -/
theorem cuspHeckeLinear_primePower_recurrence (Q : ℕ) [NeZero Q] (k : ℤ)
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (r : ℕ) :
    cuspHeckeLinear Q k (p ^ (r + 2)) =
      cuspHeckeLinear Q k p * cuspHeckeLinear Q k (p ^ (r + 1)) -
        heckeDivisorWeight Q k p • cuspHeckeLinear Q k (p ^ r) := by
  rw [cuspHeckeLinear_prime Q k hp]
  simp only [cuspHeckeLinear_primePower Q k hp, cuspHeckePrimePower]

/-- Two actual prime cusp operators commute, including primes dividing the level. -/
theorem cuspHeckeLinear_prime_commute (Q : ℕ) [NeZero Q] (k : ℤ)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Commute (cuspHeckeLinear Q k p) (cuspHeckeLinear Q k q) := by
  by_cases he : p = q
  · subst q
    exact Commute.refl _
  have hc : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr (by
    intro hd
    exact he ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one))
  change _ * _ = _ * _
  rw [cuspHeckeLinear_coprime_mul Q k hp.ne_zero hq.ne_zero hc,
    cuspHeckeLinear_coprime_mul Q k hq.ne_zero hp.ne_zero hc.symm, Nat.mul_comm]

/-- Commuting with the genuine prime operator implies commuting with each prime-power operator. -/
theorem commute_cuspHeckePrimePower {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (A : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k))
    (hA : Commute A (cuspHeckePrimeLinear k hp)) (r : ℕ) :
    Commute A (cuspHeckePrimePower k hp r) := by
  induction r using Nat.twoStepInduction with
  | zero => exact Commute.one_right A
  | one => exact hA
  | more r ih0 ih1 => exact (hA.mul_right ih1).sub_right (ih0.smul_right _)

/-- An actual prime operator commutes with every classical same-level cusp operator. -/
theorem cuspHeckeLinear_prime_commute_all (Q : ℕ) [NeZero Q] (k : ℤ)
    {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    Commute (cuspHeckeLinear Q k p) (cuspHeckeLinear Q k n) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => rw [cuspHeckeLinear_zero]; exact Commute.zero_right _
  | prime_pow q r hq =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    rw [cuspHeckeLinear_primePower Q k hq]
    apply commute_cuspHeckePrimePower hq
    rw [← cuspHeckeLinear_prime Q k hq]
    exact cuspHeckeLinear_prime_commute Q k hp hq
  | coprime a b ha hb hab iha ihb =>
    rw [← cuspHeckeLinear_coprime_mul Q k (by omega) (by omega) hab]
    exact iha.mul_right ihb

/-- All genuine classical cusp Hecke operators commute. -/
theorem cuspHeckeLinear_commute (Q : ℕ) [NeZero Q] (k : ℤ) (m n : ℕ) :
    Commute (cuspHeckeLinear Q k m) (cuspHeckeLinear Q k n) := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => rw [cuspHeckeLinear_zero]; exact Commute.zero_left _
  | prime_pow p r hp =>
    haveI : NeZero p := ⟨hp.ne_zero⟩
    rw [cuspHeckeLinear_primePower Q k hp]
    apply Commute.symm
    apply commute_cuspHeckePrimePower hp
    rw [← cuspHeckeLinear_prime Q k hp]
    exact (cuspHeckeLinear_prime_commute_all Q k hp n).symm
  | coprime a b ha hb hab iha ihb =>
    rw [← cuspHeckeLinear_coprime_mul Q k (by omega) (by omega) hab]
    exact iha.mul_left ihb

end
end Dubon2026
