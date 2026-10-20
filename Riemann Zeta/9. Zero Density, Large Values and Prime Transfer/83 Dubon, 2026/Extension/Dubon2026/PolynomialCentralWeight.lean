import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Recovering numerator degree from the actual central scaling law.
This is the polynomial degree step in the finite-generation chain for
the exact integral Borel-induced coefficient module. An infinite-order
scalar distinguishes the integral weights of actual monomials.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Scaling every original variable multiplies an actual monomial by the scalar to its total degree. -/
theorem polynomialCentralScale_monomial (a r : R) (d : σ →₀ ℕ) :
    MvPolynomial.aeval (fun i : σ => C a * X i) (monomial d r) =
      monomial d (a ^ d.degree * r) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  change C r * d.prod (fun i e => (C a * X i) ^ e) = _
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, map_mul, map_pow, Finsupp.degree_apply]
  ring

/-- The actual coefficient of a scaled polynomial records precisely its original monomial's total degree. -/
theorem polynomialCentralScale_coeff (a : R) (P : MvPolynomial σ R) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.aeval (fun i : σ => C a * X i) P) =
      a ^ d.degree * MvPolynomial.coeff d P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]
  | monomial e r =>
    rw [polynomialCentralScale_monomial]
    by_cases h : e = d
    · subst e; simp
    · simp [MvPolynomial.coeff_monomial, h]

/-- An actual central eigenpolynomial for an infinite-order scalar is homogeneous of its stated integral weight. -/
theorem polynomialCentralWeight_isHomogeneous [IsDomain R]
    (u : Rˣ) (hu : Function.Injective (fun w : ℤ => u ^ w))
    (P : MvPolynomial σ R) (w : ℤ)
    (hP : MvPolynomial.aeval (fun i : σ => C (u : R) * X i) P =
      ((u ^ w : Rˣ) : R) • P) : P.IsHomogeneous w.toNat := by
  intro d hd
  have hc := congrArg (MvPolynomial.coeff d) hP
  rw [polynomialCentralScale_coeff, MvPolynomial.coeff_smul, smul_eq_mul] at hc
  have hv : (u ^ (d.degree : ℤ) : Rˣ) = u ^ w := by
    apply Units.ext
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using mul_right_cancel₀ hd hc
  have hw := hu hv
  rw [← hw, Int.toNat_natCast]
  simpa only [Pi.one_def] using
    (DFunLike.congr_fun (Finsupp.degree_eq_weight_one (σ := σ) (R := ℕ)) d).symm

end
end Dubon2026
