import Dubon2026.SpectralFormalSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Data.Nat.Factorization.Basic

/-! # Actual multiplicative assembly of local Euler coefficients -/

namespace Dubon2026

noncomputable section
open scoped ComplexOrder

/-- Assemble literal local coefficients through the unique prime factorization, with zero
at the excluded Dirichlet index zero. -/
def assembledEulerCoefficient (c : ℕ → ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod c

/-- The excluded Dirichlet coefficient is zero. -/
theorem assembledEulerCoefficient_zero (c : ℕ → ℕ → ℂ) : assembledEulerCoefficient c 0 = 0 := by
  simp [assembledEulerCoefficient]

/-- The actual empty factorization gives coefficient one. -/
theorem assembledEulerCoefficient_one (c : ℕ → ℕ → ℂ) : assembledEulerCoefficient c 1 = 1 := by
  simp [assembledEulerCoefficient]

/-- Disjoint prime support proves multiplicativity of the constructed coefficients. -/
theorem assembledEulerCoefficient_mul (c : ℕ → ℕ → ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    assembledEulerCoefficient c (m * n) = assembledEulerCoefficient c m * assembledEulerCoefficient c n := by
  by_cases hm : m = 0
  · simp [hm, assembledEulerCoefficient_zero]
  by_cases hn : n = 0
  · simp [hn, assembledEulerCoefficient_zero]
  rw [assembledEulerCoefficient, if_neg (mul_ne_zero hm hn), assembledEulerCoefficient, if_neg hm,
    assembledEulerCoefficient, if_neg hn, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index_of_disjoint
    (by simpa only [Nat.support_factorization] using hmn.disjoint_primeFactors) c

/-- At every prime power, assembly recovers exactly the supplied literal local coefficient. -/
theorem assembledEulerCoefficient_prime_pow (c : ℕ → ℕ → ℂ) (hc : ∀ p, c p 0 = 1)
    {p : ℕ} (hp : Nat.Prime p) (r : ℕ) : assembledEulerCoefficient c (p ^ r) = c p r := by
  rw [assembledEulerCoefficient, if_neg (pow_ne_zero r hp.ne_zero), hp.factorization_pow]
  exact Finsupp.prod_single_index (hc p)

/-- Real nonnegative local coefficients give real nonnegative actual Dirichlet coefficients. -/
theorem assembledEulerCoefficient_nonneg (c : ℕ → ℕ → ℂ)
    (hc : ∀ p r, 0 ≤ c p r) (n : ℕ) : 0 ≤ assembledEulerCoefficient c n := by
  by_cases hn : n = 0
  · simp [hn, assembledEulerCoefficient_zero]
  rw [assembledEulerCoefficient, if_neg hn, Finsupp.prod]
  exact Finset.prod_nonneg (fun p _ => hc p _)

/-- Uniform local prime-power bounds multiply to an actual polynomial bound in the index. -/
theorem assembledEulerCoefficient_norm_le (c : ℕ → ℕ → ℂ) (d : ℕ)
    (hc : ∀ p : ℕ, Nat.Prime p → ∀ r : ℕ, ‖c p r‖ ≤ ((p : ℝ) ^ r) ^ d)
    (n : ℕ) (hn : n ≠ 0) : ‖assembledEulerCoefficient c n‖ ≤ (n : ℝ) ^ d := by
  rw [assembledEulerCoefficient, if_neg hn, Finsupp.prod, norm_prod]
  calc
    _ ≤ ∏ p ∈ n.factorization.support, ((p : ℝ) ^ n.factorization p) ^ d := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      exact hc p (Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp)) _
    _ = (∏ p ∈ n.factorization.support, (p : ℝ) ^ n.factorization p) ^ d := by rw [Finset.prod_pow]
    _ = (n : ℝ) ^ d := by
      congr 1
      exact_mod_cast Nat.prod_factorization_pow_eq_self hn

/-- The actual coefficient sequence has a finite abscissa of absolute convergence. -/
theorem assembledEulerCoefficient_abscissa_le (c : ℕ → ℕ → ℂ) (d : ℕ)
    (hc : ∀ p : ℕ, Nat.Prime p → ∀ r : ℕ, ‖c p r‖ ≤ ((p : ℝ) ^ r) ^ d) :
    LSeries.abscissaOfAbsConv (assembledEulerCoefficient c) ≤ (d : ℝ) + 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
  refine ⟨1, fun n hn => ?_⟩
  simpa only [one_mul, Real.rpow_natCast] using assembledEulerCoefficient_norm_le c d hc n hn

/-- The assembled actual Dirichlet series has exactly the supplied local Euler series. -/
theorem assembledEulerCoefficient_hasProd (c : ℕ → ℕ → ℂ) (hc : ∀ p, c p 0 = 1)
    {s : ℂ} (hs : LSeriesSummable (assembledEulerCoefficient c) s) :
    HasProd (fun p : Nat.Primes => ∑' r : ℕ, c p r * ((((p : ℕ) : ℂ) ^ (-s)) ^ r))
      (LSeries (assembledEulerCoefficient c) s) := by
  have hsum : Summable (fun n : ℕ => assembledEulerCoefficient c n * (n : ℂ) ^ (-s)) := by
    exact hs.congr (fun n => LSeries.term_def₀ (assembledEulerCoefficient_zero c) s n)
  have hh := EulerProduct.eulerProduct_hasProd
    (f := fun n : ℕ => assembledEulerCoefficient c n * (n : ℂ) ^ (-s))
    (by simp [assembledEulerCoefficient_one])
    (fun {m n} hmn => by
      dsimp only
      rw [assembledEulerCoefficient_mul c hmn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      ring)
    hsum.norm (by simp [assembledEulerCoefficient_zero])
  have he (p : Nat.Primes) (r : ℕ) :
      assembledEulerCoefficient c ((p : ℕ) ^ r) * (((p : ℕ) ^ r : ℕ) : ℂ) ^ (-s) =
        c p r * ((((p : ℕ) : ℂ) ^ (-s)) ^ r) := by
    rw [assembledEulerCoefficient_prime_pow c hc p.property, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  simpa only [he, LSeries, LSeries.term_def₀ (assembledEulerCoefficient_zero c)] using hh

end
end Dubon2026
