import Dubon2026.TorusPolynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # The genuine multivariate polynomial underlying the Bohr lift -/

namespace Dubon2026

open scoped BigOperators

noncomputable section

/-- Natural prime valuations as a finitely supported monomial exponent. -/
def bohrExponent (N n : ℕ) : PrimeCoordinate N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p => n.factorization p.val)

theorem bohrExponent_apply (N n : ℕ) (p : PrimeCoordinate N) :
    bohrExponent N n p = n.factorization p.val := rfl

theorem bohrExponent_eq_zero_iff {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    bohrExponent N n = 0 ↔ n = 1 := by
  have h : bohrExponent N n = 0 ↔ primeExponent N n = 0 := by
    simp only [Finsupp.ext_iff, bohrExponent_apply, Finsupp.zero_apply, funext_iff,
      primeExponent, Pi.zero_apply, Nat.cast_eq_zero]
  exact h.trans (primeExponent_eq_zero_iff hn hnN)

/-- The finite multivariate polynomial with the source's actual weighted coefficients. -/
def bohrPolynomial (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) : MvPolynomial (PrimeCoordinate N) ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    MvPolynomial.monomial (bohrExponent N n) (a n * (n : ℂ) ^ (-(σ : ℂ)))

theorem eval_bohrPolynomial (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z : PrimeCoordinate N → ℂ) :
    MvPolynomial.eval z (bohrPolynomial a N σ) = bohrLift a N σ z := by
  simp only [bohrPolynomial, map_sum, MvPolynomial.eval_monomial, bohrLift, bohrMonomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), bohrExponent_apply]

theorem coeff_zero_bohrPolynomial (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    MvPolynomial.coeff 0 (bohrPolynomial a N σ) = a 1 := by
  classical
  rw [bohrPolynomial, MvPolynomial.coeff_sum]
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      MvPolynomial.coeff 0
        (MvPolynomial.monomial (bohrExponent N n) (a n * (n : ℂ) ^ (-(σ : ℂ)))) =
      if n = 1 then a 1 else 0 := by
    simp only [MvPolynomial.coeff_monomial,
      bohrExponent_eq_zero_iff (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
    split_ifs with h
    · subst n
      simp
    · rfl
  rw [Finset.sum_congr rfl hterm]
  simp [hN]

theorem bohrPolynomial_ne_zero {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) :
    bohrPolynomial a N σ ≠ 0 := by
  intro h
  have hc := coeff_zero_bohrPolynomial a hN σ
  rw [h, MvPolynomial.coeff_zero] at hc
  exact ha hc.symm

/-- Evaluation of any multivariate polynomial on the normalized unit-circle coordinates. -/
def polynomialOnTorus {ι : Type*} (p : MvPolynomial ι ℂ) : C(UnitAddTorus ι, ℂ) where
  toFun z := MvPolynomial.eval (fun i => fourier 1 (z i)) p
  continuous_toFun := p.continuous_eval.comp (continuous_pi fun i =>
    (fourier 1).continuous.comp (continuous_apply i))

theorem polynomialOnTorus_bohrPolynomial (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) :
    polynomialOnTorus (bohrPolynomial a N σ) = bohrOnTorus a N σ := by
  ext z
  exact eval_bohrPolynomial a N σ (fun p => fourier 1 (z p))

end

end Dubon2026
