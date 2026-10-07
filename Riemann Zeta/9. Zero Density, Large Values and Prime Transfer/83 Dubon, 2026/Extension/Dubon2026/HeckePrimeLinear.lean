import Dubon2026.HeckePrimeInvariance
import Dubon2026.PrimitiveCuspForms

/-! # Linearity and Fourier coefficients of the genuine prime Hecke endomorphism -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Finset
open scoped MatrixGroups ModularForm

noncomputable section

/-- The literal upper averaging operator is additive. -/
theorem heckeAverage_add (d : ℕ) [NeZero d] (f g : ℍ → ℂ) (τ : ℍ) :
    heckeAverage d (f + g) τ = heckeAverage d f τ + heckeAverage d g τ := by
  simp [heckeAverage, Finset.sum_add_distrib, mul_add]

/-- The literal upper averaging operator is complex linear in its function. -/
theorem heckeAverage_smul (d : ℕ) [NeZero d] (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    heckeAverage d (c • f) τ = c * heckeAverage d f τ := by
  simp only [heckeAverage, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- Each divisor term is additive. -/
theorem classicalHeckeTerm_add (Q : ℕ) (k : ℤ) (n d : ℕ) (hd : d ∈ n.divisors)
    (f g : ℍ → ℂ) (τ : ℍ) :
    classicalHeckeTerm Q k n d hd (f + g) τ =
      classicalHeckeTerm Q k n d hd f τ + classicalHeckeTerm Q k n d hd g τ := by
  dsimp only [classicalHeckeTerm]
  split_ifs <;> simp [heckeAverage_add, mul_add]

/-- Each divisor term is complex linear in its function. -/
theorem classicalHeckeTerm_smul (Q : ℕ) (k : ℤ) (n d : ℕ) (hd : d ∈ n.divisors)
    (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    classicalHeckeTerm Q k n d hd (c • f) τ = c * classicalHeckeTerm Q k n d hd f τ := by
  dsimp only [classicalHeckeTerm]
  split_ifs
  · rw [heckeAverage_smul]; ring
  · rw [mul_zero]

/-- The actual finite classical Hecke function is additive for every index. -/
theorem classicalHeckeFunction_add (Q : ℕ) (k : ℤ) (n : ℕ) (f g : ℍ → ℂ) (τ : ℍ) :
    classicalHeckeFunction Q k n (f + g) τ =
      classicalHeckeFunction Q k n f τ + classicalHeckeFunction Q k n g τ := by
  simp only [classicalHeckeFunction, classicalHeckeTerm_add, Finset.sum_add_distrib]

/-- The actual finite classical Hecke function respects complex scalars at every index. -/
theorem classicalHeckeFunction_smul (Q : ℕ) (k : ℤ) (n : ℕ) (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    classicalHeckeFunction Q k n (c • f) τ = c * classicalHeckeFunction Q k n f τ := by
  simp only [classicalHeckeFunction, classicalHeckeTerm_smul, Finset.mul_sum]

/-- The genuine prime Hecke operator as a complex linear endomorphism of the cusp space. -/
def cuspHeckePrimeLinear {Q p : ℕ} [NeZero Q] [NeZero p] (k : ℤ) (hp : Nat.Prime p) :
    CuspForm ((Gamma0 Q).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma0 Q).map (mapGL ℝ)) k where
  toFun := cuspHeckePrime hp
  map_add' f g := CuspForm.ext (fun τ => classicalHeckeFunction_add Q k p f g τ)
  map_smul' c f := CuspForm.ext (fun τ => classicalHeckeFunction_smul Q k p c f τ)

/-- The actual prime Hecke cusp form has exactly the classical Fourier divisor sum. -/
theorem cuspHeckePrime_coeff {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (m : ℕ) :
    cuspCoefficients (cuspHeckePrime hp f) m = classicalHeckeCoefficient Q k p (cuspCoefficients f) m := by
  exact (ModularFormClass.qExpansion_coeff_unique (f := cuspHeckePrime hp f) zero_lt_one
    (by simp : (1 : ℝ) ∈ ((Gamma0 Q).map (mapGL ℝ)).strictPeriods)
    (fun τ => hasSum_classicalHeckeFunction Q k p f (cuspCoefficients f) τ
      (fun σ => by simpa only [smul_eq_mul] using cuspCoefficients_hasSum f σ)) m).symm

/-- Normalized primitive forms are actual eigenvectors of the bundled good-prime operator. -/
theorem primitiveCuspForm_prime_eigenvector {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    cuspHeckePrimeLinear k hp f.toCuspForm = cuspCoefficients f.toCuspForm p • f.toCuspForm := by
  apply CuspForm.ext
  intro τ
  exact cuspHeckeEigenform_normalized_action f.toCuspForm f.normalized f.isEigen hp.pos hpQ τ

/-- The prime Fourier divisor sum has exactly its two classical terms. -/
theorem classicalHeckeCoefficient_prime (Q : ℕ) (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (a : ℕ → ℂ) (m : ℕ) :
    classicalHeckeCoefficient Q k p a m = a (p * m) +
      if Nat.Coprime p Q ∧ p ∣ m then (p : ℂ) ^ (k - 1) * a (m / p) else 0 := by
  simp [classicalHeckeCoefficient, hp.divisors, hp.ne_one.symm, Nat.div_self hp.pos]

/-- The genuine prime Hecke cusp form has the classical two-term Fourier formula. -/
theorem cuspHeckePrime_coeff_prime {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (m : ℕ) :
    cuspCoefficients (cuspHeckePrime hp f) m = cuspCoefficients f (p * m) +
      if Nat.Coprime p Q ∧ p ∣ m then (p : ℂ) ^ (k - 1) * cuspCoefficients f (m / p) else 0 := by
  rw [cuspHeckePrime_coeff, classicalHeckeCoefficient_prime Q k hp]

end
end Dubon2026
