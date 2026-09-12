import Tao2026.Asymptotics
import Tao2026.Intervals

/-!
# Literal finite counting functions

The paper counts values in `[1,x]`. These definitions keep value counts
separate from counts of intervals or representations.
-/

namespace Tao2026

/-- Cardinality of `S ∩ [1,x]`. -/
noncomputable def countUpTo (S : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter fun n => n ∈ S).card

/-- Real-valued form of `countUpTo`, for asymptotic predicates. -/
noncomputable def countUpToReal (S : Set ℕ) (x : ℕ) : ℝ := countUpTo S x

noncomputable def badCount (x : ℕ) : ℕ := countUpTo badSet x

noncomputable def nontrivialBadCount (x : ℕ) : ℕ :=
  countUpTo (badSet \ badOneTermSet) x

noncomputable def badOneTermCount (x : ℕ) : ℕ := countUpTo badOneTermSet x

noncomputable def veryBadCount (x : ℕ) : ℕ := countUpTo veryBadSet x

noncomputable def nontrivialVeryBadCount (x : ℕ) : ℕ :=
  countUpTo (veryBadSet \ veryBadOneTermSet) x

noncomputable def veryBadOneTermCount (x : ℕ) : ℕ :=
  countUpTo veryBadOneTermSet x

noncomputable def factorialThreeCount (x : ℕ) : ℕ :=
  countUpTo factorialThreeSet x

noncomputable def nontrivialFactorialThreeCount (x : ℕ) : ℕ :=
  countUpTo (factorialThreeSet \ factorialThreeOneTermSet) x

noncomputable def factorialThreeOneTermCount (x : ℕ) : ℕ :=
  countUpTo factorialThreeOneTermSet x

noncomputable def factorialSquareTripleCount (x : ℕ) : ℕ :=
  (factorialSquareTriplesUpTo x).card

@[simp]
theorem countUpTo_zero (S : Set ℕ) : countUpTo S 0 = 0 := by
  classical
  simp [countUpTo]

/-- Literal value counts are monotone under inclusion of sets. -/
theorem countUpTo_mono {S T : Set ℕ} (hST : S ⊆ T) (x : ℕ) :
    countUpTo S x ≤ countUpTo T x := by
  classical
  unfold countUpTo
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

/-- Literal value counts are monotone in the closed upper endpoint. -/
theorem countUpTo_mono_right {S : Set ℕ} {x y : ℕ} (hxy : x ≤ y) :
    countUpTo S x ≤ countUpTo S y := by
  classical
  unfold countUpTo
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hxy⟩, hn.2⟩

theorem factorialThreeOneTermCount_le_factorialThreeCount (x : ℕ) :
    factorialThreeOneTermCount x ≤ factorialThreeCount x :=
  countUpTo_mono factorialThreeOneTermSet_subset_factorialThreeSet x

/-- If `T ⊆ S`, the literal value count of `S` splits exactly into the
non-`T` part and the `T` part. -/
theorem countUpTo_sdiff_add_countUpTo_of_subset {S T : Set ℕ}
    (hTS : T ⊆ S) (x : ℕ) :
    countUpTo (S \ T) x + countUpTo T x = countUpTo S x := by
  classical
  let sFin := (Finset.Icc 1 x).filter fun n => n ∈ S
  let tFin := (Finset.Icc 1 x).filter fun n => n ∈ T
  let dFin := (Finset.Icc 1 x).filter fun n => n ∈ S \ T
  have hsub : tFin ⊆ sFin := by
    intro n hn
    simp only [tFin, sFin, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hTS hn.2⟩
  have hdiff : sFin \ tFin = dFin := by
    ext n
    simp only [sFin, tFin, dFin, Finset.mem_sdiff, Finset.mem_filter,
      Set.mem_diff]
    tauto
  have hcard : dFin.card + tFin.card = sFin.card := by
    rw [← hdiff]
    exact Finset.card_sdiff_add_card_eq_card hsub
  have hdCount : countUpTo (S \ T) x = dFin.card := by
    unfold countUpTo
    congr 1
    ext n
    simp only [dFin, Finset.mem_filter]
  have htCount : countUpTo T x = tFin.card := by
    unfold countUpTo
    congr 1
  have hsCount : countUpTo S x = sFin.card := by
    unfold countUpTo
    congr 1
  rw [hdCount, htCount, hsCount]
  exact hcard

theorem nontrivialBadCount_add_badOneTermCount (x : ℕ) :
    nontrivialBadCount x + badOneTermCount x = badCount x :=
  countUpTo_sdiff_add_countUpTo_of_subset badOneTermSet_subset_badSet x

theorem nontrivialVeryBadCount_add_veryBadOneTermCount (x : ℕ) :
    nontrivialVeryBadCount x + veryBadOneTermCount x = veryBadCount x :=
  countUpTo_sdiff_add_countUpTo_of_subset veryBadOneTermSet_subset_veryBadSet x

theorem nontrivialFactorialThreeCount_add_factorialThreeOneTermCount (x : ℕ) :
    nontrivialFactorialThreeCount x + factorialThreeOneTermCount x =
      factorialThreeCount x :=
  countUpTo_sdiff_add_countUpTo_of_subset
    factorialThreeOneTermSet_subset_factorialThreeSet x

end Tao2026
