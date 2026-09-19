import Tao2026.BurgessWeilPrimeKummerRootMultisetEigenvalues

/-!
# Explicit root-multiset Kummer correlations

This file removes the polynomial wrapper from the higher-root branch.  Over
an arbitrary finite extension, the correlation is the literal sum of the
product of the local character powers indexed by the root support, with each
power equal to the corresponding multiset count.

The direct correlation sequence is proved equal to the polynomial Kummer
sequence in every degree.  The remaining higher-root source is therefore
equivalent to a fixed vector of integral weight-one eigenvalues realizing
these explicit finite sums.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def finiteFieldRootMultisetCorrelation
    (K L : Type*) [Field K] [DecidableEq K] [Field L] [Fintype L]
    [Algebra K L] (ψ : MulChar L ℂ) (R : Multiset K) : ℂ :=
  ∑ x : L, ∏ r ∈ R.toFinset,
    (ψ ^ R.count r) (x - algebraMap K L r)

theorem finiteFieldPolynomialCharacterCorrelation_primeKummerRootMultisetPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (R : Multiset (ZMod p))
    (L : Type*) [Field L] [Fintype L] [DecidableEq L]
    [Algebra (ZMod p) L] (ψ : MulChar L ℂ) :
    finiteFieldPolynomialCharacterCorrelation L ψ
        ((primeKummerRootMultisetPolynomial R).map
          (algebraMap (ZMod p) L)) =
      finiteFieldRootMultisetCorrelation (ZMod p) L ψ R := by
  unfold finiteFieldPolynomialCharacterCorrelation
  unfold finiteFieldRootMultisetCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  rw [eval_map_eq_rootProduct
    (primeKummerRootMultisetPolynomial R)
    (primeKummerRootMultisetPolynomial_splits R) x]
  rw [(primeKummerRootMultisetPolynomial_monic R).leadingCoeff,
    map_one, one_mul, primeKummerRootMultisetPolynomial_roots]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r hr
  rw [primeKummerRootMultisetPolynomial_rootMultiplicity,
    map_pow]
  exact (MulChar.pow_apply' ψ
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hr)).ne'
      (x - algebraMap (ZMod p) L r)).symm

def primeRootMultisetExtensionCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : ℕ → ℂ
  | 0 => finiteFieldRootMultisetCorrelation (ZMod p) (ZMod p) χ R
  | q + 1 => by
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact finiteFieldRootMultisetCorrelation (ZMod p) E χE R

theorem primeKummerExtensionCorrelation_eq_rootMultiset
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    ∀ q : ℕ,
      primeKummerExtensionCorrelation p χ
          (primeKummerRootMultisetPolynomial R) q =
        primeRootMultisetExtensionCorrelation p χ R q
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero]
      simpa [primePolynomialCharacterCorrelation,
        primeRootMultisetExtensionCorrelation] using
        (finiteFieldPolynomialCharacterCorrelation_primeKummerRootMultisetPolynomial
          R (ZMod p) χ)
  | q + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift]
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change finiteFieldPolynomialCharacterCorrelation E χE
          ((primeKummerRootMultisetPolynomial R).map
            (algebraMap (ZMod p) E)) =
        finiteFieldRootMultisetCorrelation (ZMod p) E χE R
      exact finiteFieldPolynomialCharacterCorrelation_primeKummerRootMultisetPolynomial
        R E χE

structure PrimeKummerExplicitRootMultisetEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) where
  eigenvalue : Fin (R.toFinset.card - 1) → ℂ
  integral : ∀ i, IsIntegral ℤ (eigenvalue i)
  weight_le : ∀ i, ‖eigenvalue i‖ ≤ Real.sqrt p
  trace_eq : ∀ q : ℕ,
    primeRootMultisetExtensionCorrelation p χ R q =
      -∑ i, eigenvalue i ^ (q + 1)

theorem PrimeKummerExplicitRootMultisetEigenvalues.extension_norm_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (e : PrimeKummerExplicitRootMultisetEigenvalues p χ R) (q : ℕ) :
    ‖primeRootMultisetExtensionCorrelation p χ R q‖ ≤
      ((R.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p ^ (q + 1) := by
  rw [e.trace_eq q, norm_neg]
  calc
    ‖∑ i, e.eigenvalue i ^ (q + 1)‖ ≤
        ∑ i, ‖e.eigenvalue i ^ (q + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (R.toFinset.card - 1),
        Real.sqrt p ^ (q + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (e.weight_le i) _
    _ = ((R.toFinset.card - 1 : ℕ) : ℝ) *
        Real.sqrt p ^ (q + 1) := by simp

def PrimeKummerRootMultisetEigenvalues.toExplicit
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (e : PrimeKummerRootMultisetEigenvalues p χ R) :
    PrimeKummerExplicitRootMultisetEigenvalues p χ R where
  eigenvalue := e.eigenvalue
  integral := e.integral
  weight_le := e.weight_le
  trace_eq q := by
    rw [← primeKummerExtensionCorrelation_eq_rootMultiset p χ R q]
    exact e.trace_eq q

def PrimeKummerExplicitRootMultisetEigenvalues.toPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (e : PrimeKummerExplicitRootMultisetEigenvalues p χ R) :
    PrimeKummerRootMultisetEigenvalues p χ R where
  eigenvalue := e.eigenvalue
  integral := e.integral
  weight_le := e.weight_le
  trace_eq q := by
    rw [primeKummerExtensionCorrelation_eq_rootMultiset p χ R q]
    exact e.trace_eq q

theorem nonempty_primeKummerRootMultisetEigenvalues_iff_explicit
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    Nonempty (PrimeKummerRootMultisetEigenvalues p χ R) ↔
      Nonempty (PrimeKummerExplicitRootMultisetEigenvalues p χ R) := by
  constructor
  · exact fun h => h.map PrimeKummerRootMultisetEigenvalues.toExplicit
  · exact fun h => h.map
      PrimeKummerExplicitRootMultisetEigenvalues.toPolynomial

def TaoPrimeKummerExplicitRootMultisetEigenvaluesFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        Nonempty (PrimeKummerExplicitRootMultisetEigenvalues p χ R)

theorem taoPrimeKummerNormalizedRootMultisetEigenvaluesFourRootsOrMore_iff_explicit :
    TaoPrimeKummerNormalizedRootMultisetEigenvaluesFourRootsOrMore ↔
      TaoPrimeKummerExplicitRootMultisetEigenvaluesFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerRootMultisetEigenvalues_iff_explicit.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerRootMultisetEigenvalues_iff_explicit.mpr
      (h p χ R hχ hzero hone hcard hreduced)

def TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues : Prop :=
  TaoPrimePowerLegendreEigenpair ∧
    TaoPrimeKummerExplicitRootMultisetEigenvaluesFourRootsOrMore

theorem taoPrimeKummerEigenpairOrRootMultisetEigenvalues_iff_explicit :
    TaoPrimeKummerEigenpairOrRootMultisetEigenvalues ↔
      TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues := by
  rw [TaoPrimeKummerEigenpairOrRootMultisetEigenvalues,
    TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues,
    taoPrimeKummerNormalizedRootMultisetEigenvaluesFourRootsOrMore_iff_explicit]

theorem TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues.toFull
    (h : TaoPrimeKummerExplicitEigenpairOrRootMultisetEigenvalues) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerEigenpairOrRootMultisetEigenvalues.toFull
    (taoPrimeKummerEigenpairOrRootMultisetEigenvalues_iff_explicit.mpr h)

end
end Tao2026
