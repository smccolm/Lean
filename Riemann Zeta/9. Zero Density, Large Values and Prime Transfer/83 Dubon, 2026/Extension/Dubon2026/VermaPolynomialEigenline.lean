import Dubon2026.VermaPolynomialLieAction
import Mathlib.Tactic.LinearCombination

/-! # The genuine highest-weight line and full central action of the polynomial Verma module -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R : Type*} [CommRing R]

/-- Every original polynomial coefficient has its exact Verma Cartan weight. -/
theorem vermaPolynomialH_coeff (μ : R) (p : R[X]) (n : ℕ) :
    (vermaPolynomialH μ p).coeff n = (μ - 2 * n) * p.coeff n := by
  cases n with
  | zero => simp [vermaPolynomialH_apply, mul_assoc]
  | succ n =>
      simp only [vermaPolynomialH_apply, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul,
        coeff_derivative, Nat.cast_add, Nat.cast_one]
      ring

/-- In a characteristic-zero domain, the genuine top Cartan eigenspace consists exactly of the original constant polynomials. -/
theorem vermaPolynomial_top_weight_line [IsDomain R] [CharZero R] (μ : R) (p : R[X])
    (he : vermaPolynomialH μ p = μ • p) : p = C (p.coeff 0) := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => simp only [coeff_C_zero]
  | succ n =>
      have hc := congrArg (fun q : R[X] => q.coeff (n + 1)) he
      dsimp only at hc
      rw [vermaPolynomialH_coeff, coeff_smul, smul_eq_mul] at hc
      have hz : (2 * ((n + 1 : ℕ) : R)) * p.coeff (n + 1) = 0 := by linear_combination -hc
      have hn : (2 : R) * ((n + 1 : ℕ) : R) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (show (2 : ℕ) ≠ 0 by decide))
          (by exact_mod_cast Nat.succ_ne_zero n)
      simpa only [coeff_C, Nat.add_one_ne_zero, if_false] using (mul_eq_zero.mp hz).resolve_left hn

variable [Algebra ℂ R]

/-- The genuine matrix center commutes with the original polynomial compact Cartan action. -/
theorem vermaPolynomial_center_commutes_H (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    Commute (vermaPolynomialH μ) (vermaPolynomialEnvelopingAction μ z.val) := by
  have hz : Commute (UniversalEnvelopingAlgebra.ι ℂ compactSl2H) z.val :=
    Subalgebra.mem_center_iff.mp z.property _
  have hh := hz.map (vermaPolynomialEnvelopingAction μ)
  rw [vermaPolynomialEnvelopingAction_generator, vermaPolynomialLieAction_H] at hh
  simpa only [neg_neg] using hh.neg_left

/-- Every original central translate of the actual Verma generator belongs to the original constant-polynomial line. -/
theorem vermaPolynomial_center_generator [IsDomain R] [CharZero R] (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    vermaPolynomialEnvelopingAction μ z.val 1 =
      C ((vermaPolynomialEnvelopingAction μ z.val 1).coeff 0) := by
  apply vermaPolynomial_top_weight_line μ
  have hh := LinearMap.congr_fun (vermaPolynomial_center_commutes_H μ z).eq (1 : R[X])
  change vermaPolynomialH μ (vermaPolynomialEnvelopingAction μ z.val 1) =
    vermaPolynomialEnvelopingAction μ z.val (vermaPolynomialH μ 1) at hh
  rw [(vermaPolynomial_generator μ).1, map_smul] at hh
  exact hh

end
end Dubon2026
