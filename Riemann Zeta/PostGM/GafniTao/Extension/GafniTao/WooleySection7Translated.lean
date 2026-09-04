import GafniTao.WooleySection7Valuation
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The translated and dilated top equations in Wooley Section 7

This file makes the substitutions in (7.9)--(7.10) literal.  Constants are
removed before taking tuple displacements, and every coefficient acquires
the exact factor `p^(a*i)` under `t ↦ p^a t`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The top `r` normal-form equations `Phi_(k-r+l)` from (7.7), with Lean's
zero-based index `l`. -/
def wooleySection7TopSystem
    (k r p c : ℕ) (psi : Fin r → Polynomial ℤ) :
    WooleyPolynomialSystem r := fun l =>
  X ^ (wooleySection7Node k r l + 1) +
    C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l

/-- Translation by `h`, dilation by `p^a`, and removal of the constant term.
This is the polynomial whose tuple displacement occurs in (7.10). -/
def wooleySection7TranslatedDilatedPolynomial
    (p a : ℕ) (h : ℤ) (phi : Polynomial ℤ) : Polynomial ℤ :=
  (taylor h phi).comp (C ((p : ℤ) ^ a) * X) - C (phi.eval h)

theorem wooleySection7TranslatedDilatedPolynomial_eval
    (p a : ℕ) (h y : ℤ) (phi : Polynomial ℤ) :
    (wooleySection7TranslatedDilatedPolynomial p a h phi).eval y =
      phi.eval ((p : ℤ) ^ a * y + h) - phi.eval h := by
  simp [wooleySection7TranslatedDilatedPolynomial, taylor_eval]

theorem wooleySection7TranslatedDilatedPolynomial_eq_comp
    (p a : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    wooleySection7TranslatedDilatedPolynomial p a h phi =
      (wooleyTaylorDifference h phi).comp (C ((p : ℤ) ^ a) * X) := by
  simp [wooleySection7TranslatedDilatedPolynomial,
    wooleyTaylorDifference]

theorem wooleySection7TranslatedDilatedPolynomial_coeff_zero
    (p a : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    (wooleySection7TranslatedDilatedPolynomial p a h phi).coeff 0 = 0 := by
  unfold wooleySection7TranslatedDilatedPolynomial
  rw [coeff_sub, comp_C_mul_X_coeff, coeff_C, pow_zero, mul_one,
    taylor_coeff]
  simp

/-- Exact coefficient scaling under the substitution in (7.9). -/
theorem wooleySection7TranslatedDilatedPolynomial_coeff_succ
    (p a i : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    (wooleySection7TranslatedDilatedPolynomial p a h phi).coeff (i + 1) =
      (taylor h phi).coeff (i + 1) *
        (p : ℤ) ^ (a * (i + 1)) := by
  unfold wooleySection7TranslatedDilatedPolynomial
  rw [coeff_sub, comp_C_mul_X_coeff, coeff_C]
  rw [if_neg (by omega : i + 1 ≠ 0), sub_zero]
  rw [pow_mul]

/-- Constants cancel from equal-length tuple displacements, so evaluating
the translated polynomial is exactly the original top equation after (7.9). -/
theorem wooleySection7TranslatedDilatedPolynomial_tupleDisplacement
    {I : Type*} (p a R : ℕ) (h : ℤ) (phi : Polynomial ℤ)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R
        (fun x => phi.eval ((p : ℤ) ^ a * point x + h)) xy =
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TranslatedDilatedPolynomial p a h phi).eval
            (point x)) xy := by
  simp only [wooleyIntegerTupleDisplacement,
    wooleySection7TranslatedDilatedPolynomial_eval]
  simp_rw [sum_sub_distrib]
  ring

/-- Exact low-degree plus tail decomposition of a translated top equation.
No asymptotic or unspecified remainder is introduced. -/
theorem wooleySection7TranslatedDilatedPolynomial_decomposition
    (p a r : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    wooleySection7TranslatedDilatedPolynomial p a h phi =
      ∑ i : Fin r,
        C ((taylor h phi).coeff ((i : ℕ) + 1) *
          (p : ℤ) ^ (a * ((i : ℕ) + 1))) * X ^ ((i : ℕ) + 1) +
      X ^ (r + 1) *
        wooleyPolynomialTail (r + 1)
          (wooleySection7TranslatedDilatedPolynomial p a h phi) := by
  let g := wooleySection7TranslatedDilatedPolynomial p a h phi
  have hdeg : (wooleyPolynomialLowPart (r + 1) g).natDegree < r + 1 :=
    wooleyPolynomialLowPart_natDegree_lt (Nat.zero_lt_succ r) g
  have hlow : wooleyPolynomialLowPart (r + 1) g =
      ∑ i : Fin r,
        C ((taylor h phi).coeff ((i : ℕ) + 1) *
          (p : ℤ) ^ (a * ((i : ℕ) + 1))) * X ^ ((i : ℕ) + 1) := by
    rw [(wooleyPolynomialLowPart (r + 1) g).as_sum_range_C_mul_X_pow' hdeg]
    rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    rw [wooleyPolynomialLowPart_coeff (by omega)]
    change C (g.coeff 0) + _ = _
    rw [show g.coeff 0 = 0 by
      exact wooleySection7TranslatedDilatedPolynomial_coeff_zero p a h phi,
      C_0, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [wooleyPolynomialLowPart_coeff (by omega)]
    rw [show g.coeff ((i : ℕ) + 1) =
        (taylor h phi).coeff ((i : ℕ) + 1) *
          (p : ℤ) ^ (a * ((i : ℕ) + 1)) by
      exact wooleySection7TranslatedDilatedPolynomial_coeff_succ p a i h phi]
  change g = _
  calc
    g = wooleyPolynomialLowPart (r + 1) g +
        X ^ (r + 1) * wooleyPolynomialTail (r + 1) g :=
      (wooleyPolynomial_low_add_tail (r + 1) g).symm
    _ = _ := by rw [hlow]

/-- A decomposition that exposes the full common `p^(a*(r+1))` factor in
the high-degree tail.  This factor is the source of the spacing gain in
(7.11). -/
theorem wooleySection7TranslatedDilatedPolynomial_tail_factorization
    (p a r : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    wooleySection7TranslatedDilatedPolynomial p a h phi =
      ∑ i : Fin r,
        C ((wooleyTaylorDifference h phi).coeff ((i : ℕ) + 1) *
          (p : ℤ) ^ (a * ((i : ℕ) + 1))) * X ^ ((i : ℕ) + 1) +
      C ((p : ℤ) ^ (a * (r + 1))) * X ^ (r + 1) *
        (wooleyPolynomialTail (r + 1) (wooleyTaylorDifference h phi)).comp
          (C ((p : ℤ) ^ a) * X) := by
  rw [wooleySection7TranslatedDilatedPolynomial_eq_comp]
  calc
    (wooleyTaylorDifference h phi).comp (C ((p : ℤ) ^ a) * X) =
        (∑ i : Fin r,
            C ((wooleyTaylorDifference h phi).coeff ((i : ℕ) + 1)) *
              X ^ ((i : ℕ) + 1) +
          X ^ (r + 1) *
            wooleyPolynomialTail (r + 1) (wooleyTaylorDifference h phi)).comp
              (C ((p : ℤ) ^ a) * X) := by
      exact congrArg
        (fun f : Polynomial ℤ => f.comp (C ((p : ℤ) ^ a) * X))
        (wooleyTaylorDifference_eq_low_sum_add_tail r h phi)
    _ = _ := by
      simp only [add_comp, mul_comp]
      apply congrArg₂ (· + ·)
      · rw [Polynomial.sum_comp]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_comp, C_comp, pow_comp]
        rw [X_comp]
        rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, pow_mul]
      · simp only [pow_comp]
        rw [X_comp]
        rw [mul_pow, ← C_pow, pow_mul]

/-- Coefficient form of the exact Omega expansion after simultaneously
performing the translation and the dilation in (7.9). -/
theorem wooleySection7TranslatedTop_coeff_rat
    {k r p c a : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) :
    ((wooleySection7TranslatedDilatedPolynomial p a h
        (wooleySection7TopSystem k r p c psi l)).coeff
          ((i : ℕ) + 1) : ℚ) =
      (h : ℚ) ^
          (((wooleySection7Node k r l + 1 : ℕ) : ℤ) -
            ((((i : ℕ) + 1 : ℕ) : ℤ))) *
        (wooleySection7OmegaMatrix (p := p) (c := c)
          hrk h hh psi i l : ℚ) *
        (p : ℚ) ^ (a * ((i : ℕ) + 1)) := by
  rw [wooleySection7TranslatedDilatedPolynomial_coeff_succ]
  push_cast
  unfold wooleySection7TopSystem
  rw [(wooleySection7OmegaEntry_spec
    (p := p) (c := c) hrk h hh psi i l).1]
  rw [show
    (((wooleySection7Node k r l + 1 : ℕ) : ℤ) -
        ((((i : ℕ) + 1 : ℕ) : ℤ))) =
      (wooleySection7Node k r l : ℤ) - (i : ℤ) by omega]
  simp only [wooleySection7OmegaMatrix]
  ring

/-- Full translated-and-dilated top equation in the coefficient form used
immediately after (7.10), including the literal high-degree polynomial tail. -/
theorem wooleySection7TranslatedTop_expansion_rat
    {k r p c a : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) :
    Polynomial.map (Int.castRingHom ℚ)
        (wooleySection7TranslatedDilatedPolynomial p a h
          (wooleySection7TopSystem k r p c psi l)) =
      ∑ i : Fin r,
        C ((h : ℚ) ^
            (((wooleySection7Node k r l + 1 : ℕ) : ℤ) -
              ((((i : ℕ) + 1 : ℕ) : ℤ))) *
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi i l : ℚ) *
          (p : ℚ) ^ (a * ((i : ℕ) + 1))) * X ^ ((i : ℕ) + 1) +
      X ^ (r + 1) *
        Polynomial.map (Int.castRingHom ℚ)
          (wooleyPolynomialTail (r + 1)
            (wooleySection7TranslatedDilatedPolynomial p a h
              (wooleySection7TopSystem k r p c psi l))) := by
  have hdecomp := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (wooleySection7TranslatedDilatedPolynomial_decomposition
      p a r h (wooleySection7TopSystem k r p c psi l))
  rw [hdecomp]
  simp only [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  apply congrArg (fun z => z + _)
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  rw [map_mul, map_pow]
  unfold wooleySection7TopSystem
  change (((taylor h
      (X ^ (wooleySection7Node k r l + 1) +
        C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff
          ((i : ℕ) + 1) : ℤ) : ℚ) *
      (p : ℚ) ^ (a * ((i : ℕ) + 1)) = _
  rw [(wooleySection7OmegaEntry_spec
    (p := p) (c := c) hrk h hh psi i l).1]
  simp only [wooleySection7OmegaMatrix]

#print axioms wooleySection7TranslatedTop_coeff_rat
#print axioms wooleySection7TranslatedTop_expansion_rat
#print axioms wooleySection7TranslatedDilatedPolynomial_eq_comp
#print axioms wooleySection7TranslatedDilatedPolynomial_tail_factorization

#print axioms wooleySection7TranslatedDilatedPolynomial_eval
#print axioms wooleySection7TranslatedDilatedPolynomial_coeff_zero
#print axioms wooleySection7TranslatedDilatedPolynomial_coeff_succ
#print axioms wooleySection7TranslatedDilatedPolynomial_tupleDisplacement
#print axioms wooleySection7TranslatedDilatedPolynomial_decomposition

end

end GafniTao
