import Tao2026.LargeSieveSelections

/-!
# Global tensor-energy aggregation

This file identifies cyclic DFT energy on an initial interval with circle
analysis energy, then applies the separated-frequency bound to the union of
all tensor frequencies.  Its final theorem is the global upper-energy half of
Tao's Corollary 2.8 for all fixed-cardinality modulus selections.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

/-- Extend a function on `Fin L` by zero to the natural numbers. -/
def finExtend {L : ℕ} (f : Fin L → ℂ) (n : ℕ) : ℂ :=
  if h : n < L then f ⟨n, h⟩ else 0

@[simp]
theorem finExtend_apply {L : ℕ} (f : Fin L → ℂ) (n : Fin L) :
    finExtend f n = f n := by
  simp [finExtend, n.isLt]

theorem sum_finExtend_range {L : ℕ} (f : Fin L → ℂ) :
    ∑ n ∈ Finset.range L, finExtend f n = ∑ n, f n := by
  rw [← Fin.sum_univ_eq_sum_range (finExtend f) L]
  simp only [finExtend_apply]

theorem finiteAnalysis_circleCharacterVector_eq
    {A : Type*} {L : ℕ} (alpha : A → ℝ) (f : Fin L → ℂ) (a : A) :
    finiteAnalysis
        (fun a (n : Fin L) => circleCharacterVector alpha a n) f a =
      ∑ n : Fin L, standardAdditiveCharacter
        (-(((n : ℕ) : ℝ) * alpha a)) * f n := by
  unfold finiteAnalysis circleCharacterVector
  apply sum_congr rfl
  intro n hn
  congr 1
  change conj (standardAdditiveCharacter (((n : ℕ) : ℝ) * alpha a)) = _
  exact (standardAdditiveCharacter_neg _).symm

/-- The DFT of the residue aggregation of a zero-extended `Fin L` function
is exactly finite circle analysis at the corresponding rational frequency. -/
theorem cyclicDft_finExtend_eq_finiteAnalysis
    {A : Type*} {L N : ℕ} [NeZero N]
    (k : ZMod N) (f : Fin L → ℂ) (a : A)
    (alpha : A → ℝ)
    (halpha : alpha a = cyclicCircleFrequency N k) :
    ZMod.dft (residueClassSum (Finset.range L) (finExtend f)) k =
      finiteAnalysis
        (fun a (n : Fin L) => circleCharacterVector alpha a n) f a := by
  rw [dft_residueClassSum]
  rw [finiteAnalysis_circleCharacterVector_eq]
  calc
    ∑ n ∈ Finset.range L,
        ZMod.stdAddChar (-((n : ZMod N) * k)) * finExtend f n =
      ∑ n ∈ Finset.range L,
        standardAdditiveCharacter (-((n : ℝ) * alpha a)) *
          finExtend f n := by
        apply sum_congr rfl
        intro n hn
        rw [halpha,
          standardAdditiveCharacter_neg_nat_mul_cyclicCircleFrequency]
    _ = ∑ n : Fin L, standardAdditiveCharacter
        (-(((n : ℕ) : ℝ) * alpha a)) * f n := by
      symm
      simpa only [finExtend_apply] using
        (Fin.sum_univ_eq_sum_range
          (fun n => standardAdditiveCharacter (-((n : ℝ) * alpha a)) *
            finExtend f n) L)

/-- Exact reindexing of the global circle-analysis energy as the double sum
of tensor DFT energies over all modulus lists. -/
theorem sum_tensorFrequencyFamily_analysis_eq_tensorDft
    {B : Type*} [Fintype B] {qs : B → List SieveModulus}
    (hpair : ∀ i, (qs i).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    {L : ℕ} (f : Fin L → ℂ) :
    ∑ a : TensorFrequencyFamilyIndex qs,
        Complex.normSq (finiteAnalysis
          (fun a (n : Fin L) => circleCharacterVector
            (fun a => cyclicCircleFrequency
              (tensorFrequencyFamilyModulus a)
              (tensorFrequencyFamilyCyclic hpair a)) a n) f a) =
      ∑ i : B, ∑ ξ ∈ tensorNonzeroFrequencies (qs i),
        Complex.normSq (tensorDft (qs i)
          (tensorResidueClassSum (qs i) (Finset.range L)
            (finExtend f)) ξ) := by
  classical
  change (∑ a : (Σ i, ↥(tensorNonzeroFrequencies (qs i))), _) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i hi
  rw [Finset.sum_subtype (tensorNonzeroFrequencies (qs i))
    (fun _ => Iff.rfl)]
  apply sum_congr rfl
  intro ξ hξ
  rw [tensorDft_residueClassSum_eq_cyclicDft
    (qs i) (hpair i) (Finset.range L) (finExtend f) ξ.1]
  rw [cyclicDft_finExtend_eq_finiteAnalysis
    (a := ⟨i, ξ⟩)
    (alpha := fun a => cyclicCircleFrequency
      (tensorFrequencyFamilyModulus a)
      (tensorFrequencyFamilyCyclic hpair a))]
  rfl

/-- Global tensor-energy upper bound over a family of modulus lists satisfying
the exclusive-modulus and denominator-product hypotheses. -/
theorem sum_tensorDft_le_tensorFrequencyFamily
    {B : Type*} [Fintype B] {qs : B → List SieveModulus}
    {L : ℕ} (hL : 0 < L)
    (hpair : ∀ i, (qs i).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (hexclusive : ∀ i j, i ≠ j → ∃ q ∈ qs i,
      ∀ r ∈ qs j, q.modulus.Coprime r.modulus)
    (hprod : ∀ i j,
      sieveModulusProduct (qs i) * sieveModulusProduct (qs j) ≤ L)
    (f : Fin L → ℂ) :
    ∑ i : B, ∑ ξ ∈ tensorNonzeroFrequencies (qs i),
        Complex.normSq (tensorDft (qs i)
          (tensorResidueClassSum (qs i) (Finset.range L)
            (finExtend f)) ξ) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  rw [← sum_tensorFrequencyFamily_analysis_eq_tensorDft hpair f]
  exact circleAnalysis_energy_le_tensorFrequencyFamily hL
    hpair hexclusive hprod f

/-- Global upper-energy half of Corollary 2.8 for every `k`-element modulus
selection, with no loss proportional to the number of selections. -/
theorem sum_tensorDft_le_fixedCardSelections
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus)
    (hbase : ∀ q r, q ≠ r →
      (modulus q).modulus.Coprime (modulus r).modulus)
    {k K L : ℕ} (hL : 0 < L)
    (hprod : ∀ s : FixedCardModulusSelections Q k,
      sieveModulusProduct (selectedModuliList modulus s) ≤ K)
    (hK : K * K ≤ L) (f : Fin L → ℂ) :
    ∑ s : FixedCardModulusSelections Q k,
      ∑ ξ ∈ tensorNonzeroFrequencies (selectedModuliList modulus s),
        Complex.normSq (tensorDft (selectedModuliList modulus s)
          (tensorResidueClassSum (selectedModuliList modulus s)
            (Finset.range L) (finExtend f)) ξ) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  exact sum_tensorDft_le_tensorFrequencyFamily hL
    (fun s => selectedModuliList_pairwise modulus hbase s)
    (fun s t hst => selectedModuliList_exclusive modulus hbase s t hst)
    (selectedModuliList_product_pair_le modulus hprod hK) f

/-- Global Montgomery uncertainty after summing the lower tensor bounds over
all selections and applying the one global large-sieve upper bound. -/
theorem montgomery_global_uncertainty_fixedCardSelections
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus)
    (hbase : ∀ q r, q ≠ r →
      (modulus q).modulus.Coprime (modulus r).modulus)
    {k K L : ℕ} (hL : 0 < L)
    (hprod : ∀ s : FixedCardModulusSelections Q k,
      sieveModulusProduct (selectedModuliList modulus s) ≤ K)
    (hK : K * K ≤ L)
    (R : (s : FixedCardModulusSelections Q k) →
      SieveRestrictions (selectedModuliList modulus s))
    (hproper : ∀ s, SieveRestrictionsProper (R s))
    (f : Fin L → ℂ)
    (hzero : ∀ (s : FixedCardModulusSelections Q k) (n : Fin L),
      ¬ SieveAvoids (R s)
          (natSieveCube (selectedModuliList modulus s) n) →
        f n = 0) :
    (∑ s : FixedCardModulusSelections Q k, sieveRestrictionRatio (R s)) *
        Complex.normSq (∑ n, f n) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  have hlower :
      ∑ s : FixedCardModulusSelections Q k,
          sieveRestrictionRatio (R s) *
            Complex.normSq (∑ n ∈ Finset.range L, finExtend f n) ≤
        ∑ s : FixedCardModulusSelections Q k,
          ∑ ξ ∈ tensorNonzeroFrequencies (selectedModuliList modulus s),
            Complex.normSq (tensorDft (selectedModuliList modulus s)
              (tensorResidueClassSum (selectedModuliList modulus s)
                (Finset.range L) (finExtend f)) ξ) := by
    apply Finset.sum_le_sum
    intro s hs
    exact montgomery_uncertainty_tensor_finite
      (selectedModuliList modulus s) (R s) (Finset.range L)
      (finExtend f) (hproper s) (by
        intro n hn hnot
        have hnL : n < L := Finset.mem_range.mp hn
        simp only [finExtend, hnL, ↓reduceDIte]
        exact hzero s ⟨n, hnL⟩ hnot)
  calc
    (∑ s : FixedCardModulusSelections Q k, sieveRestrictionRatio (R s)) *
          Complex.normSq (∑ n, f n) =
        ∑ s : FixedCardModulusSelections Q k,
          sieveRestrictionRatio (R s) *
            Complex.normSq (∑ n ∈ Finset.range L, finExtend f n) := by
      rw [sum_finExtend_range]
      rw [Finset.sum_mul]
    _ ≤ ∑ s : FixedCardModulusSelections Q k,
          ∑ ξ ∈ tensorNonzeroFrequencies (selectedModuliList modulus s),
            Complex.normSq (tensorDft (selectedModuliList modulus s)
              (tensorResidueClassSum (selectedModuliList modulus s)
                (Finset.range L) (finExtend f)) ξ) := hlower
    _ ≤ (8 * L : ℝ) * ∑ n, Complex.normSq (f n) :=
      sum_tensorDft_le_fixedCardSelections modulus hbase hL hprod hK f

/-- Finite survivor-cardinality form of Corollary 2.8. -/
theorem montgomery_global_survivor_card_fixedCardSelections
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus)
    (hbase : ∀ q r, q ≠ r →
      (modulus q).modulus.Coprime (modulus r).modulus)
    {k K L : ℕ} (hL : 0 < L)
    (hprod : ∀ s : FixedCardModulusSelections Q k,
      sieveModulusProduct (selectedModuliList modulus s) ≤ K)
    (hK : K * K ≤ L)
    (R : (s : FixedCardModulusSelections Q k) →
      SieveRestrictions (selectedModuliList modulus s))
    (hproper : ∀ s, SieveRestrictionsProper (R s))
    (survivors : Finset (Fin L))
    (havoid : ∀ n ∈ survivors,
      ∀ s : FixedCardModulusSelections Q k,
      SieveAvoids (R s)
        (natSieveCube (selectedModuliList modulus s) n)) :
    (∑ s : FixedCardModulusSelections Q k, sieveRestrictionRatio (R s)) *
        (survivors.card : ℝ) ≤ 8 * L := by
  let f : Fin L → ℂ := fun n => if n ∈ survivors then 1 else 0
  have hglobal := montgomery_global_uncertainty_fixedCardSelections
    modulus hbase hL hprod hK R hproper f (by
      intro s n hnot
      by_cases hn : n ∈ survivors
      · exact (hnot (havoid n hn s)).elim
      · simp [f, hn])
  have hsum : ∑ n, f n = (survivors.card : ℂ) := by
    simp [f]
  have henergy : ∑ n, Complex.normSq (f n) =
      (survivors.card : ℝ) := by
    simp [f]
  have hglobal' :
      (∑ s : FixedCardModulusSelections Q k,
          sieveRestrictionRatio (R s)) * (survivors.card : ℝ) ^ 2 ≤
        (8 * L : ℝ) * survivors.card := by
    rw [hsum, henergy] at hglobal
    simpa only [Complex.normSq_natCast, pow_two] using hglobal
  by_cases hcard : survivors.card = 0
  · simp [hcard]
  · have hcardPos : (0 : ℝ) < survivors.card := by positivity
    apply le_of_mul_le_mul_right _ hcardPos
    simpa only [pow_two, mul_assoc] using hglobal'

end

end Tao2026
