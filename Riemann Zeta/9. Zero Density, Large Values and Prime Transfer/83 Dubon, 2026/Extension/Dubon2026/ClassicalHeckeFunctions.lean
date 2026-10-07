import Dubon2026.HeckeAveraging
import Mathlib.NumberTheory.Divisors

/-! # Classical Hecke functions with trivial character

The operator is the actual finite sum over ad=n of d^(-1) a^(k-1)
Σ_{b<d} f((az+b)/d), retaining exactly the terms coprime(a,Q)=1.
It acts on functions on the upper half-plane; preservation of the bundled cusp
space is not assumed or claimed by its definition. The convergent q-expansion
and eigenvalue/coefficient bridges use this literal analytic function.
-/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Finset
open scoped MatrixGroups ModularForm

noncomputable section

/-- A divisor summand in the classical finite Hecke formula. -/
def classicalHeckeTerm (Q : ℕ) (k : ℤ) (n d : ℕ) (hd : d ∈ n.divisors)
    (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  haveI : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
  haveI : NeZero (n / d) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
      (Nat.dvd_of_mem_divisors hd))
    (Nat.pos_of_mem_divisors hd)).ne'⟩
  if Nat.Coprime d Q then (d : ℂ) ^ (k - 1) *
    heckeAverage (n / d) f (levelRaiseMatrix d • τ) else 0

/-- The actual classical T_n finite sum, with bad-prime terms removed by coprimality. -/
def classicalHeckeFunction (Q : ℕ) (k : ℤ) (n : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑ d ∈ n.divisors.attach, classicalHeckeTerm Q k n d.val d.property f τ

/-- The classical Fourier divisor sum attached to T_n. -/
def classicalHeckeCoefficient (Q : ℕ) (k : ℤ) (n : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, if Nat.Coprime d Q ∧ d ∣ m then
    (d : ℂ) ^ (k - 1) * a ((n / d) * (m / d)) else 0

/-- The Fourier expansion of one actual divisor summand. -/
theorem hasSum_classicalHeckeTerm (Q : ℕ) (k : ℤ) (n d : ℕ) (hd : d ∈ n.divisors)
    (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf : ∀ σ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 (σ : ℂ) ^ m) (f σ)) :
    HasSum (fun m => (if Nat.Coprime d Q ∧ d ∣ m then
      (d : ℂ) ^ (k - 1) * a ((n / d) * (m / d)) else 0) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (classicalHeckeTerm Q k n d hd f τ) := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have hn0 := (Nat.mem_divisors.mp hd).2
  have hdn := (Nat.mem_divisors.mp hd).1
  haveI : NeZero d := ⟨hd0.ne'⟩
  haveI : NeZero (n / d) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hd0).ne'⟩
  by_cases hc : Nat.Coprime d Q
  · have hs := hasSum_heckeAverage (n / d) f a (levelRaiseMatrix d • τ) hf
    rw [coe_levelRaiseMatrix_smul, qParam_nat_mul_eq_pow] at hs
    have hh := (hasSum_pow_dvd_reindex hd0 hs).const_smul ((d : ℂ) ^ (k - 1))
    convert hh using 1
    · funext m
      dsimp only
      by_cases hm : d ∣ m <;> simp [hc, hm, smul_eq_mul, mul_assoc]
    · dsimp only [classicalHeckeTerm]
      rw [if_pos hc]
      rfl
  · simp [classicalHeckeTerm, hc]

/-- Finite Hecke summation preserves the genuine convergent Fourier representation. -/
theorem hasSum_classicalHeckeFunction (Q : ℕ) (k : ℤ) (n : ℕ)
    (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf : ∀ σ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 (σ : ℂ) ^ m) (f σ)) :
    HasSum (fun m => classicalHeckeCoefficient Q k n a m •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (classicalHeckeFunction Q k n f τ) := by
  have hs := hasSum_sum (s := n.divisors.attach)
    (fun d _ => hasSum_classicalHeckeTerm Q k n d.val d.property f a τ hf)
  convert hs using 1
  funext m
  dsimp only
  simp only [classicalHeckeCoefficient, smul_eq_mul, ← Finset.sum_mul]
  congr 1
  exact (Finset.sum_attach n.divisors _).symm

/-- The first Hecke coefficient is a(n), for every positive n including bad primes. -/
theorem classicalHeckeCoefficient_one (Q : ℕ) (k : ℤ) {n : ℕ} (hn : n ≠ 0)
    (a : ℕ → ℂ) : classicalHeckeCoefficient Q k n a 1 = a n := by
  rw [classicalHeckeCoefficient, Finset.sum_eq_single 1]
  · simp
  · intro d _ hd1
    simp [Nat.dvd_one, hd1]
  · intro hn1
    exact (hn1 (Nat.one_mem_divisors.mpr hn)).elim

/-- Coefficients of an actual Hecke eigenfunction satisfy the divisor-sum identity. -/
theorem cusp_hecke_eigenfunction_coefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) (eigenvalue : ℂ)
    (he : ∀ τ, classicalHeckeFunction Q k n f τ = eigenvalue * f τ) (m : ℕ) :
    classicalHeckeCoefficient Q k n (cuspCoefficients f) m = eigenvalue * cuspCoefficients f m := by
  have hsum (τ : ℍ) : HasSum (fun j => classicalHeckeCoefficient Q k n (cuspCoefficients f) j •
      Function.Periodic.qParam 1 (τ : ℂ) ^ j) ((eigenvalue • f) τ) := by
    simpa only [he τ, CuspForm.coe_smul, Pi.smul_apply, smul_eq_mul] using
      hasSum_classicalHeckeFunction Q k n f (cuspCoefficients f) τ
        (fun σ => by simpa only [smul_eq_mul] using cuspCoefficients_hasSum f σ)
  have hu := ModularFormClass.qExpansion_coeff_unique (f := eigenvalue • f)
    zero_lt_one (by simp : (1 : ℝ) ∈ ((Gamma0 Q).map (mapGL ℝ)).strictPeriods) hsum m
  calc classicalHeckeCoefficient Q k n (cuspCoefficients f) m
      = cuspCoefficients (eigenvalue • f) m := hu
    _ = eigenvalue * cuspCoefficients f m := (cuspCoefficientLinear Q k m).map_smul eigenvalue f

/-- For a normalized actual eigenfunction, its eigenvalue equals its nth Fourier coefficient. -/
theorem cusp_hecke_eigenvalue_eq_coefficient {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hf : cuspCoefficients f 1 = 1)
    {n : ℕ} (hn : n ≠ 0) (eigenvalue : ℂ)
    (he : ∀ τ, classicalHeckeFunction Q k n f τ = eigenvalue * f τ) : eigenvalue = cuspCoefficients f n := by
  have hc := cusp_hecke_eigenfunction_coefficients f n eigenvalue he 1
  rw [classicalHeckeCoefficient_one Q k hn, hf, mul_one] at hc
  exact hc.symm

end
end Dubon2026
