import Dubon2026.PrimitiveFullEigen

/-! # Full classical coefficient identities derived from genuine primitive forms -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Every positive-index classical coefficient transform acts by the actual primitive Fourier coefficient. -/
theorem primitiveCuspForm_hecke_coefficient_all {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) {n : ℕ} (hn : 0 < n) (m : ℕ) :
    classicalHeckeCoefficient N k n (cuspCoefficients f.toCuspForm) m =
      cuspCoefficients f.toCuspForm n * cuspCoefficients f.toCuspForm m := by
  have hc := congrArg (cuspCoefficientLinear N k m) (primitiveCuspForm_eigenvector_all f hn)
  change cuspCoefficients (cuspHecke n f.toCuspForm) m =
    cuspCoefficientLinear N k m (cuspCoefficients f.toCuspForm n • f.toCuspForm) at hc
  rw [cuspHecke_coeff, map_smul] at hc
  exact hc

/-- Genuine primitive Fourier coefficients are multiplicative at every coprime pair, including bad indices. -/
theorem primitiveCuspForm_coefficient_mul_all {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (n m : ℕ) (hnm : n.Coprime m) :
    cuspCoefficients f.toCuspForm (n * m) =
      cuspCoefficients f.toCuspForm n * cuspCoefficients f.toCuspForm m := by
  by_cases hn : n = 0
  · subst n
    rw [zero_mul, cuspCoefficients_zero, zero_mul]
  · have hc := primitiveCuspForm_hecke_coefficient_all f (Nat.pos_of_ne_zero hn) m
    rwa [classicalHeckeCoefficient_coprime N k hn hnm] at hc

/-- At a prime dividing the level, the actual coefficient transform has its true single-term recurrence. -/
theorem primitiveCuspForm_bad_prime_mul {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) {p : ℕ} (hp : Nat.Prime p) (hpN : p ∣ N) (m : ℕ) :
    cuspCoefficients f.toCuspForm (p * m) =
      cuspCoefficients f.toCuspForm p * cuspCoefficients f.toCuspForm m := by
  have hc := primitiveCuspForm_hecke_coefficient_all f hp.pos m
  have hn : ¬ p.Coprime N := fun h => hp.coprime_iff_not_dvd.mp h hpN
  simpa only [classicalHeckeCoefficient_prime N k hp, hn, false_and, if_false, add_zero] using hc

/-- The bad-prime power coefficients are exactly powers of the genuine first prime coefficient. -/
theorem primitiveCuspForm_bad_prime_power {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) {p : ℕ} (hp : Nat.Prime p) (hpN : p ∣ N) (r : ℕ) :
    cuspCoefficients f.toCuspForm (p ^ r) = cuspCoefficients f.toCuspForm p ^ r := by
  induction r with
  | zero => simpa only [pow_zero] using f.normalized
  | succ r ih => rw [pow_succ', primitiveCuspForm_bad_prime_mul f hp hpN, ih, pow_succ']

/-- Every genuine primitive form has the classical good/bad prime-power recurrence. -/
theorem primitiveCuspForm_primePower_recurrence {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) {p : ℕ} (hp : Nat.Prime p) (r : ℕ) :
    cuspCoefficients f.toCuspForm (p ^ (r + 2)) =
      cuspCoefficients f.toCuspForm p * cuspCoefficients f.toCuspForm (p ^ (r + 1)) -
        heckeDivisorWeight N k p * cuspCoefficients f.toCuspForm (p ^ r) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have he := LinearMap.congr_fun (cuspHeckeLinear_primePower_recurrence N k hp r) f.toCuspForm
  change cuspHeckeLinear N k (p ^ (r + 2)) f.toCuspForm =
    cuspHeckeLinear N k p (cuspHeckeLinear N k (p ^ (r + 1)) f.toCuspForm) -
      heckeDivisorWeight N k p • cuspHeckeLinear N k (p ^ r) f.toCuspForm at he
  rw [primitiveCuspForm_eigenvector_all f (pow_pos hp.pos _),
    primitiveCuspForm_eigenvector_all f (pow_pos hp.pos _), map_smul,
    primitiveCuspForm_eigenvector_all f hp.pos,
    primitiveCuspForm_eigenvector_all f (pow_pos hp.pos _)] at he
  have hc := congrArg (cuspCoefficientLinear N k 1) he
  simp only [map_smul, map_sub, smul_eq_mul, show cuspCoefficientLinear N k 1 f.toCuspForm = 1 from f.normalized,
    mul_one] at hc
  simpa only [mul_comm] using hc

end
end Dubon2026
