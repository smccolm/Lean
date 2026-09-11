import Tao2026.LargeSieveRational
import Mathlib.Data.Finset.Dedup

/-!
# Fixed-cardinality modulus selections

This file instantiates the global rational-frequency large sieve on all
fixed-cardinality subsets of a finite pairwise-coprime modulus family.
Distinct subsets automatically supply the exclusive modulus needed for CRT
frequency distinctness.
-/

open Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The finite type of `k`-element subsets of a finite modulus index type. -/
def FixedCardModulusSelections (Q : Type*) [Fintype Q]
    [DecidableEq Q] (k : ℕ) :=
  {s : Finset Q // s.card = k}

noncomputable instance fixedCardModulusSelectionsFintype
    (Q : Type*) [Fintype Q] [DecidableEq Q] (k : ℕ) :
    Fintype (FixedCardModulusSelections Q k) := by
  unfold FixedCardModulusSelections
  infer_instance

/-- Ordered list of packaged moduli belonging to a finite selection. -/
def selectedModuliList {Q : Type*} [Fintype Q]
    [DecidableEq Q] (modulus : Q → SieveModulus)
    {k : ℕ} (s : FixedCardModulusSelections Q k) :
    List SieveModulus :=
  s.1.toList.map modulus

theorem selectedModuliList_pairwise
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus)
    (hbase : ∀ q r, q ≠ r →
      (modulus q).modulus.Coprime (modulus r).modulus)
    {k : ℕ} (s : FixedCardModulusSelections Q k) :
    (selectedModuliList modulus s).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus) := by
  rw [selectedModuliList, List.pairwise_map]
  exact s.1.nodup_toList.pairwise_of_forall_ne (by
    intro q hq r hr hqr
    exact hbase q r hqr)

/-- Two unequal fixed-cardinality selections have a modulus in the first but
not the second, and that modulus is coprime to every modulus in the second. -/
theorem selectedModuliList_exclusive
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus)
    (hbase : ∀ q r, q ≠ r →
      (modulus q).modulus.Coprime (modulus r).modulus)
    {k : ℕ} (s t : FixedCardModulusSelections Q k)
    (hst : s ≠ t) :
    ∃ q ∈ selectedModuliList modulus s,
      ∀ r ∈ selectedModuliList modulus t,
        q.modulus.Coprime r.modulus := by
  have hfinneq : s.1 ≠ t.1 := by
    intro h
    exact hst (Subtype.ext h)
  have hex : ∃ q, q ∈ s.1 ∧ q ∉ t.1 := by
    by_contra h
    push Not at h
    have hsub : s.1 ⊆ t.1 := by
      intro q hqs
      exact h q hqs
    have heq : s.1 = t.1 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [s.2, t.2])
    exact hfinneq heq
  rcases hex with ⟨q, hqs, hqt⟩
  refine ⟨modulus q, ?_, ?_⟩
  · rw [selectedModuliList, List.mem_map]
    exact ⟨q, Finset.mem_toList.mpr hqs, rfl⟩
  · intro r hr
    rw [selectedModuliList, List.mem_map] at hr
    rcases hr with ⟨u, hut, rfl⟩
    have hqu : q ≠ u := by
      intro h
      subst u
      exact hqt (Finset.mem_toList.mp hut)
    exact hbase q u hqu

theorem selectedModuliList_product_pair_le
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus) {k K L : ℕ}
    (hprod : ∀ s : FixedCardModulusSelections Q k,
      sieveModulusProduct (selectedModuliList modulus s) ≤ K)
    (hK : K * K ≤ L) :
    ∀ s t : FixedCardModulusSelections Q k,
      sieveModulusProduct (selectedModuliList modulus s) *
        sieveModulusProduct (selectedModuliList modulus t) ≤ L := by
  intro s t
  exact (Nat.mul_le_mul (hprod s) (hprod t)).trans hK

/-- Global large-sieve upper bound over all nonzero tensor frequencies from
all `k`-element selections.  The bound pays no factor for the number of
selections. -/
theorem circleAnalysis_energy_le_fixedCardTensorSelections
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (modulus : Q → SieveModulus)
    (hbase : ∀ q r, q ≠ r →
      (modulus q).modulus.Coprime (modulus r).modulus)
    {k K L : ℕ} (hL : 0 < L)
    (hprod : ∀ s : FixedCardModulusSelections Q k,
      sieveModulusProduct (selectedModuliList modulus s) ≤ K)
    (hK : K * K ≤ L) (f : Fin L → ℂ) :
    ∑ a : TensorFrequencyFamilyIndex
        (fun s : FixedCardModulusSelections Q k =>
          selectedModuliList modulus s),
        Complex.normSq (finiteAnalysis
          (fun a (n : Fin L) => circleCharacterVector
            (fun a => cyclicCircleFrequency
              (tensorFrequencyFamilyModulus a)
              (tensorFrequencyFamilyCyclic
                (fun s => selectedModuliList_pairwise
                  modulus hbase s) a)) a n) f a) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  classical
  exact circleAnalysis_energy_le_tensorFrequencyFamily hL
    (fun s => selectedModuliList_pairwise modulus hbase s)
    (fun s t hst => selectedModuliList_exclusive modulus hbase s t hst)
    (selectedModuliList_product_pair_le modulus hprod hK) f

end

end Tao2026
