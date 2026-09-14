import Tao2026.BurgessWeilPrime
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Polynomial form of the prime Burgess Weil boundary

This file converts the remaining quotient-character sum over `ZMod p` into
the standard polynomial form used by the Weil bound.  The denominator is
raised to `orderOf χ - 1`; a uniquely occurring tagged root then has
multiplicity `1` or `orderOf χ - 1`, so the polynomial cannot be an
`orderOf χ`-th power.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The numerator product of tagged linear factors over the prime field. -/
def primeLinearNumeratorPolynomial
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) : Polynomial (ZMod p) :=
  Finset.univ.prod
    (fun i : Fin r => Polynomial.X + Polynomial.C (b (Sum.inl i)))

/-- The denominator product of tagged linear factors over the prime field. -/
def primeLinearDenominatorPolynomial
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) : Polynomial (ZMod p) :=
  Finset.univ.prod
    (fun i : Fin r => Polynomial.X + Polynomial.C (b (Sum.inr i)))

/-- Clear the inverse character by raising the denominator polynomial to one
less than the order of the character. -/
def primeLinearOrderPolynomial
    (p r : ℕ) (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) : Polynomial (ZMod p) :=
  primeLinearNumeratorPolynomial p r b *
    primeLinearDenominatorPolynomial p r b ^ (orderOf χ - 1)

/-- A complete multiplicative-character sum attached to a polynomial. -/
def primePolynomialCharacterCorrelation
    (p : ℕ) [NeZero p] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) : ℂ :=
  ∑ x : ZMod p, χ (P.eval x)

theorem eval_primeLinearNumeratorPolynomial
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) (x : ZMod p) :
    (primeLinearNumeratorPolynomial p r b).eval x =
      Finset.univ.prod (fun i : Fin r => x + b (Sum.inl i)) := by
  simp [primeLinearNumeratorPolynomial, Polynomial.eval_prod]

theorem eval_primeLinearDenominatorPolynomial
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) (x : ZMod p) :
    (primeLinearDenominatorPolynomial p r b).eval x =
      Finset.univ.prod (fun i : Fin r => x + b (Sum.inr i)) := by
  simp [primeLinearDenominatorPolynomial, Polynomial.eval_prod]

theorem monic_primeLinearNumeratorPolynomial
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearNumeratorPolynomial p r b).Monic := by
  unfold primeLinearNumeratorPolynomial
  exact Polynomial.monic_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_add_C (b (Sum.inl i)))

theorem monic_primeLinearDenominatorPolynomial
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearDenominatorPolynomial p r b).Monic := by
  unfold primeLinearDenominatorPolynomial
  exact Polynomial.monic_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_add_C (b (Sum.inr i)))

theorem mulChar_orderOf_two_le_of_ne_one
    {R S : Type*} [CommMonoid R] [Finite Rˣ] [CommMonoidWithZero S]
    (χ : MulChar R S) (hχ : χ ≠ 1) : 2 ≤ orderOf χ := by
  have hpos := χ.orderOf_pos
  have hone : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
  omega

theorem mulChar_pow_orderOf_sub_one_eq_inv
    {R S : Type*} [CommMonoid R] [Finite Rˣ] [CommMonoidWithZero S]
    (χ : MulChar R S) : χ ^ (orderOf χ - 1) = χ⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos,
    pow_orderOf_eq_one]

/-- The quotient-character correlation is exactly a polynomial character
sum after the denominator exponent is reduced modulo the character order. -/
theorem primeLinearQuotientCorrelation_eq_polynomial
    (p r : ℕ) [NeZero p] (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (χ_ne : χ ≠ 1) :
    primeLinearQuotientCorrelation p r χ b =
      primePolynomialCharacterCorrelation p χ
        (primeLinearOrderPolynomial p r χ b) := by
  have hord : 0 < orderOf χ - 1 := by
    have htwo := mulChar_orderOf_two_le_of_ne_one χ χ_ne
    omega
  have hpow := mulChar_pow_orderOf_sub_one_eq_inv χ
  unfold primeLinearQuotientCorrelation primePolynomialCharacterCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  rw [primeLinearOrderPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    eval_primeLinearNumeratorPolynomial, eval_primeLinearDenominatorPolynomial,
    map_mul, map_pow]
  congr 1
  calc
    χ⁻¹ (Finset.univ.prod (fun i : Fin r => x + b (Sum.inr i))) =
        (χ ^ (orderOf χ - 1))
          (Finset.univ.prod (fun i : Fin r => x + b (Sum.inr i))) := by rw [hpow]
    _ = χ (Finset.univ.prod (fun i : Fin r => x + b (Sum.inr i))) ^
        (orderOf χ - 1) :=
      MulChar.pow_apply' χ hord.ne' _

/-- Root multiplicity of a positive power of a nonzero polynomial. -/
theorem rootMultiplicity_pow_of_ne_zero
    {F : Type*} [Field F] (P : Polynomial F) (a : F) (n : ℕ)
    (hP : P ≠ 0) :
    (P ^ n).rootMultiplicity a = n * P.rootMultiplicity a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul
        (mul_ne_zero (pow_ne_zero n hP) hP), ih]
      simp only [Nat.succ_mul]

theorem rootMultiplicity_eq_one_of_eval_eq_zero_of_derivative_eval_ne_zero
    {F : Type*} [Field F] (P : Polynomial F) (a : F)
    (hP : P ≠ 0) (hroot : P.eval a = 0)
    (hderiv : P.derivative.eval a ≠ 0) :
    P.rootMultiplicity a = 1 := by
  have hpos : 0 < P.rootMultiplicity a :=
    (Polynomial.rootMultiplicity_pos hP).2 hroot
  have hnot : ¬1 < P.rootMultiplicity a := by
    intro htwo
    have hboth :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).1 htwo
    exact hderiv hboth.2
  omega

theorem eval_primeLinearNumeratorPolynomial_at_unique_left
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r) :
    (primeLinearNumeratorPolynomial p r b).eval (-b (Sum.inl j)) = 0 := by
  rw [eval_primeLinearNumeratorPolynomial]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

theorem eval_derivative_primeLinearNumeratorPolynomial_ne_zero_of_unique_left
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inl j) → i = Sum.inl j) :
    (primeLinearNumeratorPolynomial p r b).derivative.eval
        (-b (Sum.inl j)) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [primeLinearNumeratorPolynomial,
    eval_derivative_prod_X_add_C_at_root
      (c := fun i : Fin r => b (Sum.inl i)) j]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_contra hzero
  have heq : b (Sum.inl i) = b (Sum.inl j) := by
    have heq' : b (Sum.inl j) = b (Sum.inl i) := by
      simpa only [neg_add_eq_zero] using hzero
    exact heq'.symm
  have htag := hunique (Sum.inl i) heq
  exact (Finset.mem_erase.mp hi).1 (Sum.inl.inj htag)

theorem eval_primeLinearDenominatorPolynomial_ne_zero_of_unique_left
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inl j) → i = Sum.inl j) :
    (primeLinearDenominatorPolynomial p r b).eval (-b (Sum.inl j)) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [eval_primeLinearDenominatorPolynomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_contra hzero
  have heq : b (Sum.inr i) = b (Sum.inl j) := by
    have heq' : b (Sum.inl j) = b (Sum.inr i) := by
      simpa only [neg_add_eq_zero] using hzero
    exact heq'.symm
  have htag := hunique (Sum.inr i) heq
  cases htag

theorem rootMultiplicity_primeLinearNumeratorPolynomial_unique_left
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inl j) → i = Sum.inl j) :
    (primeLinearNumeratorPolynomial p r b).rootMultiplicity
        (-b (Sum.inl j)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact rootMultiplicity_eq_one_of_eval_eq_zero_of_derivative_eval_ne_zero
    (primeLinearNumeratorPolynomial p r b) (-b (Sum.inl j))
    (monic_primeLinearNumeratorPolynomial p r b).ne_zero
    (eval_primeLinearNumeratorPolynomial_at_unique_left p r b j)
    (eval_derivative_primeLinearNumeratorPolynomial_ne_zero_of_unique_left
      p r hp b j hunique)

theorem rootMultiplicity_primeLinearDenominatorPolynomial_unique_left
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inl j) → i = Sum.inl j) :
    (primeLinearDenominatorPolynomial p r b).rootMultiplicity
        (-b (Sum.inl j)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  exact (eval_primeLinearDenominatorPolynomial_ne_zero_of_unique_left
    p r hp b j hunique) hroot

theorem rootMultiplicity_primeLinearOrderPolynomial_unique_left
    (p r : ℕ) [NeZero p] (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inl j) → i = Sum.inl j) :
    (primeLinearOrderPolynomial p r χ b).rootMultiplicity
        (-b (Sum.inl j)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hF := (monic_primeLinearNumeratorPolynomial p r b).ne_zero
  have hG := (monic_primeLinearDenominatorPolynomial p r b).ne_zero
  unfold primeLinearOrderPolynomial
  rw [Polynomial.rootMultiplicity_mul
    (mul_ne_zero hF (pow_ne_zero _ hG)),
    rootMultiplicity_primeLinearNumeratorPolynomial_unique_left
      p r hp b j hunique,
    rootMultiplicity_pow_of_ne_zero _ _ _ hG,
    rootMultiplicity_primeLinearDenominatorPolynomial_unique_left
      p r hp b j hunique]
  simp

theorem eval_primeLinearDenominatorPolynomial_at_unique_right
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r) :
    (primeLinearDenominatorPolynomial p r b).eval (-b (Sum.inr j)) = 0 := by
  rw [eval_primeLinearDenominatorPolynomial]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

theorem eval_derivative_primeLinearDenominatorPolynomial_ne_zero_of_unique_right
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inr j) → i = Sum.inr j) :
    (primeLinearDenominatorPolynomial p r b).derivative.eval
        (-b (Sum.inr j)) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [primeLinearDenominatorPolynomial,
    eval_derivative_prod_X_add_C_at_root
      (c := fun i : Fin r => b (Sum.inr i)) j]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_contra hzero
  have heq : b (Sum.inr i) = b (Sum.inr j) := by
    have heq' : b (Sum.inr j) = b (Sum.inr i) := by
      simpa only [neg_add_eq_zero] using hzero
    exact heq'.symm
  have htag := hunique (Sum.inr i) heq
  exact (Finset.mem_erase.mp hi).1 (Sum.inr.inj htag)

theorem eval_primeLinearNumeratorPolynomial_ne_zero_of_unique_right
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inr j) → i = Sum.inr j) :
    (primeLinearNumeratorPolynomial p r b).eval (-b (Sum.inr j)) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [eval_primeLinearNumeratorPolynomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_contra hzero
  have heq : b (Sum.inl i) = b (Sum.inr j) := by
    have heq' : b (Sum.inr j) = b (Sum.inl i) := by
      simpa only [neg_add_eq_zero] using hzero
    exact heq'.symm
  have htag := hunique (Sum.inl i) heq
  cases htag

theorem rootMultiplicity_primeLinearNumeratorPolynomial_unique_right
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inr j) → i = Sum.inr j) :
    (primeLinearNumeratorPolynomial p r b).rootMultiplicity
        (-b (Sum.inr j)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  exact (eval_primeLinearNumeratorPolynomial_ne_zero_of_unique_right
    p r hp b j hunique) hroot

theorem rootMultiplicity_primeLinearDenominatorPolynomial_unique_right
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inr j) → i = Sum.inr j) :
    (primeLinearDenominatorPolynomial p r b).rootMultiplicity
        (-b (Sum.inr j)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact rootMultiplicity_eq_one_of_eval_eq_zero_of_derivative_eval_ne_zero
    (primeLinearDenominatorPolynomial p r b) (-b (Sum.inr j))
    (monic_primeLinearDenominatorPolynomial p r b).ne_zero
    (eval_primeLinearDenominatorPolynomial_at_unique_right p r b j)
    (eval_derivative_primeLinearDenominatorPolynomial_ne_zero_of_unique_right
      p r hp b j hunique)

theorem rootMultiplicity_primeLinearOrderPolynomial_unique_right
    (p r : ℕ) [NeZero p] (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r)
    (hunique : ∀ i, b i = b (Sum.inr j) → i = Sum.inr j) :
    (primeLinearOrderPolynomial p r χ b).rootMultiplicity
        (-b (Sum.inr j)) = orderOf χ - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hF := (monic_primeLinearNumeratorPolynomial p r b).ne_zero
  have hG := (monic_primeLinearDenominatorPolynomial p r b).ne_zero
  unfold primeLinearOrderPolynomial
  rw [Polynomial.rootMultiplicity_mul
    (mul_ne_zero hF (pow_ne_zero _ hG)),
    rootMultiplicity_primeLinearNumeratorPolynomial_unique_right
      p r hp b j hunique,
    rootMultiplicity_pow_of_ne_zero _ _ _ hG,
    rootMultiplicity_primeLinearDenominatorPolynomial_unique_right
      p r hp b j hunique]
  simp

/-- At the uniquely occurring tagged root, the cleared polynomial has a
multiplicity not divisible by the character order. -/
theorem not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
    (p r : ℕ) [NeZero p] (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r)
    (hχ : χ ≠ 1) (hunique : ∀ i, b i = b j → i = j) :
    ¬ orderOf χ ∣
      (primeLinearOrderPolynomial p r χ b).rootMultiplicity (-b j) := by
  have htwo := mulChar_orderOf_two_le_of_ne_one χ hχ
  cases j with
  | inl j =>
      rw [rootMultiplicity_primeLinearOrderPolynomial_unique_left
        p r hp χ b j hunique]
      intro hdvd
      have := Nat.le_of_dvd Nat.one_pos hdvd
      omega
  | inr j =>
      rw [rootMultiplicity_primeLinearOrderPolynomial_unique_right
        p r hp χ b j hunique]
      intro hdvd
      have hpos : 0 < orderOf χ - 1 := by omega
      have := Nat.le_of_dvd hpos hdvd
      omega

/-- The polynomial representing a uniquely rooted quotient is not an
`orderOf χ`-th power. This is the exact non-power hypothesis in the classical
multiplicative-character Weil theorem. -/
theorem primeLinearOrderPolynomial_not_orderOf_power_of_unique
    (p r : ℕ) [NeZero p] (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) (j : Fin r ⊕ Fin r)
    (hχ : χ ≠ 1) (hunique : ∀ i, b i = b j → i = j) :
    ¬∃ Q : Polynomial (ZMod p),
      primeLinearOrderPolynomial p r χ b = Q ^ orderOf χ := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hpower
  rcases hpower with ⟨Q, hQ⟩
  have hP : primeLinearOrderPolynomial p r χ b ≠ 0 := by
    unfold primeLinearOrderPolynomial
    exact mul_ne_zero
      (monic_primeLinearNumeratorPolynomial p r b).ne_zero
      (pow_ne_zero _ (monic_primeLinearDenominatorPolynomial p r b).ne_zero)
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hQ, hzero, zero_pow]
    exact χ.orderOf_pos.ne'
  apply not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
    p r hp χ b j hχ hunique
  rw [hQ, rootMultiplicity_pow_of_ne_zero Q (-b j) (orderOf χ) hQ0]
  exact dvd_mul_right _ _

/-- The visibly listed roots of the two products of linear factors. -/
def primeLinearRootSet
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) : Finset (ZMod p) :=
  Finset.univ.image (fun i : Fin r ⊕ Fin r => -b i)

theorem card_primeLinearRootSet_le
    (p r : ℕ) (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearRootSet p r b).card ≤ 2 * r := by
  unfold primeLinearRootSet
  calc
    (Finset.univ.image (fun i : Fin r ⊕ Fin r => -b i)).card ≤
        (Finset.univ : Finset (Fin r ⊕ Fin r)).card := Finset.card_image_le
    _ = r + r := by simp
    _ = 2 * r := by omega

theorem primeLinearOrderPolynomial_splits
    (p r : ℕ) (χ : MulChar (ZMod p) ℂ)
    (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearOrderPolynomial p r χ b).Splits := by
  unfold primeLinearOrderPolynomial primeLinearNumeratorPolynomial
    primeLinearDenominatorPolynomial
  apply Polynomial.Splits.mul
  · exact Polynomial.Splits.prod
      (fun i _ => Polynomial.Splits.X_add_C (b (Sum.inl i)))
  · exact (Polynomial.Splits.prod
      (fun i _ => Polynomial.Splits.X_add_C (b (Sum.inr i)))).pow _

theorem eval_primeLinearOrderPolynomial_eq_zero_imp_mem_rootSet
    (p r : ℕ) [NeZero p] (hp : p.Prime)
    (χ : MulChar (ZMod p) ℂ) (b : Fin r ⊕ Fin r → ZMod p)
    (hχ : χ ≠ 1) (x : ZMod p)
    (hroot : (primeLinearOrderPolynomial p r χ b).eval x = 0) :
    x ∈ primeLinearRootSet p r b := by
  letI : Fact p.Prime := ⟨hp⟩
  have hord : 0 < orderOf χ - 1 := by
    have htwo := mulChar_orderOf_two_le_of_ne_one χ hχ
    omega
  unfold primeLinearOrderPolynomial at hroot
  rw [Polynomial.eval_mul, Polynomial.eval_pow] at hroot
  rcases mul_eq_zero.mp hroot with hnum | hden
  · rw [eval_primeLinearNumeratorPolynomial,
      Finset.prod_eq_zero_iff] at hnum
    rcases hnum with ⟨i, hi, hfactor⟩
    unfold primeLinearRootSet
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl i, Finset.mem_univ _, ?_⟩
    exact (add_eq_zero_iff_eq_neg.mp hfactor).symm
  · have hden' :
        (primeLinearDenominatorPolynomial p r b).eval x = 0 := by
      exact eq_zero_of_pow_eq_zero hden
    rw [eval_primeLinearDenominatorPolynomial,
      Finset.prod_eq_zero_iff] at hden'
    rcases hden' with ⟨i, hi, hfactor⟩
    unfold primeLinearRootSet
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr i, Finset.mem_univ _, ?_⟩
    exact (add_eq_zero_iff_eq_neg.mp hfactor).symm

theorem roots_primeLinearOrderPolynomial_subset_rootSet
    (p r : ℕ) [NeZero p] [Fact p.Prime] (hp : p.Prime)
    (χ : MulChar (ZMod p) ℂ) (b : Fin r ⊕ Fin r → ZMod p)
    (hχ : χ ≠ 1) :
    (primeLinearOrderPolynomial p r χ b).roots.toFinset ⊆
      primeLinearRootSet p r b := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x hx
  apply eval_primeLinearOrderPolynomial_eq_zero_imp_mem_rootSet
    p r hp χ b hχ x
  apply (Polynomial.mem_roots
    (by
      unfold primeLinearOrderPolynomial
      exact mul_ne_zero
        (monic_primeLinearNumeratorPolynomial p r b).ne_zero
        (pow_ne_zero _
          (monic_primeLinearDenominatorPolynomial p r b).ne_zero))).mp
  exact Multiset.mem_toFinset.mp hx

theorem card_roots_primeLinearOrderPolynomial_le
    (p r : ℕ) [NeZero p] [Fact p.Prime] (hp : p.Prime)
    (χ : MulChar (ZMod p) ℂ) (b : Fin r ⊕ Fin r → ZMod p)
    (hχ : χ ≠ 1) :
    (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ≤ 2 * r :=
  (Finset.card_le_card
    (roots_primeLinearOrderPolynomial_subset_rootSet p r hp χ b hχ)).trans
      (card_primeLinearRootSet_le p r b)

/-- Standard split-polynomial form of the one-variable multiplicative
character Weil estimate. The split hypothesis makes `roots.toFinset.card`
the number of distinct geometric roots, while the displayed multiplicity
condition rules out an `orderOf χ`-th power. -/
def TaoPrimeSplitPolynomialWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬ orderOf χ ∣ P.rootMultiplicity a →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

/-- The standard split-polynomial Weil theorem supplies the normalized
linear-quotient theorem, because its polynomial has at most `2r` distinct
roots and a root whose multiplicity is not divisible by the character order. -/
theorem TaoPrimeSplitPolynomialWeilBound.toLinearQuotient
    (hweil : TaoPrimeSplitPolynomialWeilBound) :
    TaoPrimeLinearQuotientWeilBound := by
  intro p r _ χ b j hp hr hχ hunique
  letI : Fact p.Prime := ⟨hp⟩
  rw [primeLinearQuotientCorrelation_eq_polynomial p r χ b hχ]
  calc
    ‖primePolynomialCharacterCorrelation p χ
        (primeLinearOrderPolynomial p r χ b)‖ ≤
        ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) *
          Real.sqrt p :=
      hweil p χ (primeLinearOrderPolynomial p r χ b) (-b j)
        hχ (primeLinearOrderPolynomial_splits p r χ b)
        (not_orderOf_dvd_rootMultiplicity_primeLinearOrderPolynomial_of_unique
          p r hp χ b j hχ hunique)
    _ ≤ ((4 * r : ℕ) : ℝ) * Real.sqrt p := by
      have hcard := card_roots_primeLinearOrderPolynomial_le p r hp χ b hχ
      have hnat :
          2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card ≤
            4 * r := by omega
      have hreal :
          ((2 * (primeLinearOrderPolynomial p r χ b).roots.toFinset.card : ℕ) : ℝ) ≤
            ((4 * r : ℕ) : ℝ) := by exact_mod_cast hnat
      exact mul_le_mul_of_nonneg_right hreal (Real.sqrt_nonneg p)

theorem TaoPrimeSplitPolynomialWeilBound.toComposite
    (hweil : TaoPrimeSplitPolynomialWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toLinearQuotient.toComposite

/-- The numerator product has its visible degree `r`. -/
theorem natDegree_primeLinearNumeratorPolynomial
    (p r : ℕ) [NeZero p] [Fact p.Prime]
    (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearNumeratorPolynomial p r b).natDegree = r := by
  unfold primeLinearNumeratorPolynomial
  rw [Polynomial.natDegree_prod]
  · simp
  · intro i hi
    exact (Polynomial.monic_X_add_C (b (Sum.inl i))).ne_zero

/-- The denominator product has its visible degree `r`. -/
theorem natDegree_primeLinearDenominatorPolynomial
    (p r : ℕ) [NeZero p] [Fact p.Prime]
    (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearDenominatorPolynomial p r b).natDegree = r := by
  unfold primeLinearDenominatorPolynomial
  rw [Polynomial.natDegree_prod]
  · simp
  · intro i hi
    exact (Polynomial.monic_X_add_C (b (Sum.inr i))).ne_zero

/-- Clearing the denominator makes the total degree exactly the character
order times `r`. -/
theorem natDegree_primeLinearOrderPolynomial
    (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (b : Fin r ⊕ Fin r → ZMod p) :
    (primeLinearOrderPolynomial p r χ b).natDegree = r * orderOf χ := by
  unfold primeLinearOrderPolynomial
  rw [Polynomial.natDegree_mul
      (monic_primeLinearNumeratorPolynomial p r b).ne_zero
      (pow_ne_zero _ (monic_primeLinearDenominatorPolynomial p r b).ne_zero),
    (monic_primeLinearDenominatorPolynomial p r b).natDegree_pow,
    natDegree_primeLinearNumeratorPolynomial,
    natDegree_primeLinearDenominatorPolynomial]
  have hpos := χ.orderOf_pos
  have hsplit : orderOf χ - 1 + 1 = orderOf χ := Nat.sub_add_cancel hpos
  nlinarith

/-- In particular, the total degree of the cleared Burgess polynomial is
divisible by the character order. -/
theorem orderOf_dvd_natDegree_primeLinearOrderPolynomial
    (p r : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (b : Fin r ⊕ Fin r → ZMod p) :
    orderOf χ ∣ (primeLinearOrderPolynomial p r χ b).natDegree := by
  rw [natDegree_primeLinearOrderPolynomial]
  exact dvd_mul_left _ _

end

end Tao2026
