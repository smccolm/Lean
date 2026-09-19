import Tao2026.BurgessWeilPrimeKummerRootMultiset

/-!
# Fixed maximal eigenvalue vectors for root-multiset Kummer systems

The root-multiset Frobenius system has rank at most the support cardinality
minus one.  This file removes its variable index type by padding every
smaller spectrum with zero.  The resulting eigenvalue vector has the literal
fixed type `Fin (R.toFinset.card - 1) → ℂ`.

The fixed-vector formulation is exactly equivalent to the original system,
retains integrality and weight bounds coordinatewise, and controls every
extension trace by the same power sums.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

structure PrimeKummerRootMultisetEigenvalues
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) where
  eigenvalue : Fin (R.toFinset.card - 1) → ℂ
  integral : ∀ i, IsIntegral ℤ (eigenvalue i)
  weight_le : ∀ i, ‖eigenvalue i‖ ≤ Real.sqrt p
  trace_eq : ∀ q : ℕ,
    primeKummerExtensionCorrelation p χ
        (primeKummerRootMultisetPolynomial R) q =
      -∑ i, eigenvalue i ^ (q + 1)

theorem PrimeKummerRootMultisetEigenvalues.extension_norm_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (e : PrimeKummerRootMultisetEigenvalues p χ R) (q : ℕ) :
    ‖primeKummerExtensionCorrelation p χ
        (primeKummerRootMultisetPolynomial R) q‖ ≤
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

def primeKummerPaddedRootMultisetEigenvalueNat
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R)) (i : ℕ) : ℂ :=
  if h : i < s.rank then s.eigenvalue ⟨i, h⟩ else 0

def primeKummerPaddedRootMultisetEigenvalue
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R)) :
    Fin (R.toFinset.card - 1) → ℂ := fun i =>
  primeKummerPaddedRootMultisetEigenvalueNat s i

@[simp]
theorem primeKummerPaddedRootMultisetEigenvalue_of_lt
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R))
    (i : Fin (R.toFinset.card - 1)) (hi : i.val < s.rank) :
    primeKummerPaddedRootMultisetEigenvalue s i =
      s.eigenvalue ⟨i.val, hi⟩ := by
  simp [primeKummerPaddedRootMultisetEigenvalue,
    primeKummerPaddedRootMultisetEigenvalueNat, hi]

@[simp]
theorem primeKummerPaddedRootMultisetEigenvalue_of_rank_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R))
    (i : Fin (R.toFinset.card - 1)) (hi : s.rank ≤ i.val) :
    primeKummerPaddedRootMultisetEigenvalue s i = 0 := by
  simp [primeKummerPaddedRootMultisetEigenvalue,
    primeKummerPaddedRootMultisetEigenvalueNat, Nat.not_lt.mpr hi]

theorem sum_primeKummerPaddedRootMultisetEigenvalue_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R)) (d : ℕ) (hd : 0 < d) :
    (∑ i : Fin (R.toFinset.card - 1),
        primeKummerPaddedRootMultisetEigenvalue s i ^ d) =
      ∑ i : Fin s.rank, s.eigenvalue i ^ d := by
  have hrank : s.rank ≤ R.toFinset.card - 1 := by
    simpa [primeKummerRootMultisetPolynomial_roots] using s.rank_le
  calc
    (∑ i : Fin (R.toFinset.card - 1),
        primeKummerPaddedRootMultisetEigenvalue s i ^ d) =
        ∑ i ∈ Finset.range (R.toFinset.card - 1),
          primeKummerPaddedRootMultisetEigenvalueNat s i ^ d := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => primeKummerPaddedRootMultisetEigenvalueNat s i ^ d) _
    _ = ∑ i ∈ Finset.range s.rank,
          primeKummerPaddedRootMultisetEigenvalueNat s i ^ d := by
      symm
      apply Finset.sum_subset (Finset.range_mono hrank)
      intro i hi hnot
      have hirank : s.rank ≤ i := by
        simpa [Finset.mem_range] using hnot
      simp [primeKummerPaddedRootMultisetEigenvalueNat, hirank, hd.ne']
    _ = ∑ i : Fin s.rank, s.eigenvalue i ^ d := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => primeKummerPaddedRootMultisetEigenvalueNat s i ^ d) s.rank]
      apply Finset.sum_congr rfl
      intro i hi
      simp [primeKummerPaddedRootMultisetEigenvalueNat, i.isLt]

def PrimeKummerIsotypicFrobeniusSystem.toRootMultisetEigenvalues
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R)) :
    PrimeKummerRootMultisetEigenvalues p χ R where
  eigenvalue := primeKummerPaddedRootMultisetEigenvalue s
  integral i := by
    by_cases hi : i.val < s.rank
    · rw [primeKummerPaddedRootMultisetEigenvalue_of_lt s i hi]
      exact s.integral _
    · rw [primeKummerPaddedRootMultisetEigenvalue_of_rank_le s i
        (Nat.le_of_not_gt hi)]
      exact isIntegral_zero
  weight_le i := by
    by_cases hi : i.val < s.rank
    · rw [primeKummerPaddedRootMultisetEigenvalue_of_lt s i hi]
      exact s.weight_le _
    · rw [primeKummerPaddedRootMultisetEigenvalue_of_rank_le s i
        (Nat.le_of_not_gt hi)]
      simp
  trace_eq q := by
    rw [s.extensionTrace_eq q,
      sum_primeKummerPaddedRootMultisetEigenvalue_pow s (q + 1) (by omega)]

def PrimeKummerRootMultisetEigenvalues.toFrobeniusSystem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)}
    (e : PrimeKummerRootMultisetEigenvalues p χ R) :
    PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R) where
  rank := R.toFinset.card - 1
  eigenvalue := e.eigenvalue
  rank_le := by simp [primeKummerRootMultisetPolynomial_roots]
  integral := e.integral
  weight_le := e.weight_le
  trace_eq := by
    simpa using e.trace_eq 0
  extensionTrace_eq := e.trace_eq

theorem nonempty_primeKummerRootMultisetFrobeniusSystem_iff_eigenvalues
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {R : Multiset (ZMod p)} :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerRootMultisetPolynomial R)) ↔
      Nonempty (PrimeKummerRootMultisetEigenvalues p χ R) := by
  constructor
  · exact fun h => h.map
      PrimeKummerIsotypicFrobeniusSystem.toRootMultisetEigenvalues
  · exact fun h => h.map
      PrimeKummerRootMultisetEigenvalues.toFrobeniusSystem

def TaoPrimeKummerNormalizedRootMultisetEigenvaluesFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)),
    χ ≠ 1 → 0 ∈ R → 1 ∈ R → 4 ≤ R.toFinset.card →
      (∀ r ∈ R.toFinset, R.count r < orderOf χ) →
        Nonempty (PrimeKummerRootMultisetEigenvalues p χ R)

theorem taoPrimeKummerNormalizedRootMultisetFrobeniusSystemFourRootsOrMore_iff_eigenvalues :
    TaoPrimeKummerNormalizedRootMultisetFrobeniusSystemFourRootsOrMore ↔
      TaoPrimeKummerNormalizedRootMultisetEigenvaluesFourRootsOrMore := by
  constructor
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerRootMultisetFrobeniusSystem_iff_eigenvalues.mp
      (h p χ R hχ hzero hone hcard hreduced)
  · intro h p _ _ χ R hχ hzero hone hcard hreduced
    exact nonempty_primeKummerRootMultisetFrobeniusSystem_iff_eigenvalues.mpr
      (h p χ R hχ hzero hone hcard hreduced)

def TaoPrimeKummerEigenpairOrRootMultisetEigenvalues : Prop :=
  TaoPrimePowerLegendreEigenpair ∧
    TaoPrimeKummerNormalizedRootMultisetEigenvaluesFourRootsOrMore

theorem taoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem_iff_eigenvalues :
    TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem ↔
      TaoPrimeKummerEigenpairOrRootMultisetEigenvalues := by
  rw [TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem,
    TaoPrimeKummerEigenpairOrRootMultisetEigenvalues,
    taoPrimeKummerNormalizedRootMultisetFrobeniusSystemFourRootsOrMore_iff_eigenvalues]

theorem TaoPrimeKummerEigenpairOrRootMultisetEigenvalues.toFull
    (h : TaoPrimeKummerEigenpairOrRootMultisetEigenvalues) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem.toFull
    (taoPrimeKummerEigenpairOrRootMultisetFrobeniusSystem_iff_eigenvalues.mpr h)

end
end Tao2026
