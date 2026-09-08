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

theorem factorialThreeOneTermCount_le_factorialThreeCount (x : ℕ) :
    factorialThreeOneTermCount x ≤ factorialThreeCount x :=
  countUpTo_mono factorialThreeOneTermSet_subset_factorialThreeSet x

end Tao2026
