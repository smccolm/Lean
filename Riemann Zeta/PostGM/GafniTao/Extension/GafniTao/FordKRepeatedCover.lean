import GafniTao.FordKDiagonal

/-!
# Ford Lemma 3.2: the repeated-coordinate cover

The singular class is covered by a side (`z` or `w`) and an unordered index
pair.  The collision itself remains in the target, so the choice of a first
repeated pair cannot identify two source solutions.
-/

namespace GafniTao

noncomputable section

abbrev FordIndexPair (k : ℕ) := {ij : Fin k × Fin k // ij.1 < ij.2}

abbrev FordKLeftRepeatAt
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) (ij : FordIndexPair k) :=
  {u : FordKSolution Ψ s P Q q // u.1.1.1 ij.1.1 = u.1.1.1 ij.1.2}

abbrev FordKRightRepeatAt
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) (ij : FordIndexPair k) :=
  {u : FordKSolution Ψ s P Q q // u.1.1.2 ij.1.1 = u.1.1.2 ij.1.2}

abbrev FordKRepeatedSolution
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :=
  {u : FordKSolution Ψ s P Q q //
    ¬ FordTuplePairwiseDistinct u.1.1.1 ∨
      ¬ FordTuplePairwiseDistinct u.1.1.2}

def fordKRightLeftRepeatEquiv
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) :
    FordKRightRepeatAt Ψ s P Q q ij ≃ FordKLeftRepeatAt Ψ s P Q q ij where
  toFun u := ⟨⟨((u.1.1.1.2, u.1.1.1.1), (u.1.1.2.2, u.1.1.2.1)), by
    intro j
    have h := u.1.2 j
    unfold fordPolynomialDifference fordPowerDifference at h ⊢
    simp only [Finset.sum_sub_distrib] at h ⊢
    rw [pow_succ] at h ⊢
    linear_combination -h⟩, u.2⟩
  invFun u := ⟨⟨((u.1.1.1.2, u.1.1.1.1), (u.1.1.2.2, u.1.1.2.1)), by
    intro j
    have h := u.1.2 j
    unfold fordPolynomialDifference fordPowerDifference at h ⊢
    simp only [Finset.sum_sub_distrib] at h ⊢
    rw [pow_succ] at h ⊢
    linear_combination -h⟩, u.2⟩
  left_inv u := by rfl
  right_inv u := by rfl

theorem exists_fordIndexPair_of_not_injective
    {k P : ℕ} {z : FordBox k P} (hz : ¬ Function.Injective z) :
    ∃ ij : FordIndexPair k, z ij.1.1 = z ij.1.2 := by
  unfold Function.Injective at hz
  push Not at hz
  obtain ⟨i, j, hij, hne⟩ := hz
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · exact ⟨⟨(i, j), hijlt⟩, hij⟩
  · exact ⟨⟨(j, i), hjilt⟩, hij.symm⟩

noncomputable def fordRepeatedPair
    {k P : ℕ} (z : FordBox k P) (hz : ¬ Function.Injective z) :
    FordIndexPair k :=
  Classical.choose (exists_fordIndexPair_of_not_injective hz)

theorem fordRepeatedPair_property
    {k P : ℕ} (z : FordBox k P) (hz : ¬ Function.Injective z) :
    z (fordRepeatedPair z hz).1.1 = z (fordRepeatedPair z hz).1.2 :=
  Classical.choose_spec (exists_fordIndexPair_of_not_injective hz)

def fordKRepeatedCoverMap
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    FordKRepeatedSolution Ψ s P Q q →
      (Σ ij : FordIndexPair k, FordKLeftRepeatAt Ψ s P Q q ij) ⊕
        (Σ ij : FordIndexPair k, FordKRightRepeatAt Ψ s P Q q ij) := by
  intro u
  by_cases hz : Function.Injective u.1.1.1.1
  · have hw : ¬ Function.Injective u.1.1.1.2 :=
      u.2.resolve_left (not_not_intro hz)
    exact Sum.inr ⟨fordRepeatedPair u.1.1.1.2 hw,
      ⟨u.1, fordRepeatedPair_property u.1.1.1.2 hw⟩⟩
  · exact Sum.inl ⟨fordRepeatedPair u.1.1.1.1 hz,
      ⟨u.1, fordRepeatedPair_property u.1.1.1.1 hz⟩⟩

def fordKRepeatedCoverUnderlying
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    ((Σ ij : FordIndexPair k, FordKLeftRepeatAt Ψ s P Q q ij) ⊕
      (Σ ij : FordIndexPair k, FordKRightRepeatAt Ψ s P Q q ij)) →
      FordKSolution Ψ s P Q q
  | Sum.inl u => u.2.1
  | Sum.inr u => u.2.1

theorem fordKRepeatedCoverUnderlying_map
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (u : FordKRepeatedSolution Ψ s P Q q) :
    fordKRepeatedCoverUnderlying Ψ (fordKRepeatedCoverMap Ψ u) = u.1 := by
  classical
  by_cases hz : Function.Injective u.1.1.1.1
  · simp [fordKRepeatedCoverMap, hz, fordKRepeatedCoverUnderlying]
  · simp [fordKRepeatedCoverMap, hz, fordKRepeatedCoverUnderlying]

theorem fordKRepeatedCoverMap_injective
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    Function.Injective (fordKRepeatedCoverMap Ψ :
      FordKRepeatedSolution Ψ s P Q q → _) := by
  intro u v huv
  apply Subtype.ext
  rw [← fordKRepeatedCoverUnderlying_map Ψ u,
    ← fordKRepeatedCoverUnderlying_map Ψ v, huv]

theorem fordK_repeated_card_le_pair_sum
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    Nat.card (FordKRepeatedSolution Ψ s P Q q) ≤
      2 * ∑ ij : FordIndexPair k,
        Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) := by
  let Target :=
    (Σ ij : FordIndexPair k, FordKLeftRepeatAt Ψ s P Q q ij) ⊕
      (Σ ij : FordIndexPair k, FordKRightRepeatAt Ψ s P Q q ij)
  have hcard : Nat.card (FordKRepeatedSolution Ψ s P Q q) ≤
      Nat.card Target := Nat.card_le_card_of_injective
    (fordKRepeatedCoverMap Ψ) (fordKRepeatedCoverMap_injective Ψ)
  have hright (ij : FordIndexPair k) :
      Nat.card (FordKRightRepeatAt Ψ s P Q q ij) =
        Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) :=
    Nat.card_congr (fordKRightLeftRepeatEquiv Ψ ij)
  calc
    Nat.card (FordKRepeatedSolution Ψ s P Q q) ≤ Nat.card Target := hcard
    _ = (∑ ij : FordIndexPair k,
          Nat.card (FordKLeftRepeatAt Ψ s P Q q ij)) +
        ∑ ij : FordIndexPair k,
          Nat.card (FordKRightRepeatAt Ψ s P Q q ij) := by
      simp [Target, Nat.card_sum]
    _ = 2 * ∑ ij : FordIndexPair k,
          Nat.card (FordKLeftRepeatAt Ψ s P Q q ij) := by
      simp_rw [hright]
      omega

def fordKDistinctRepeatedEquiv
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    FordKSolution Ψ s P Q q ≃
      FordKDistinctSolution Ψ s P Q q ⊕
        FordKRepeatedSolution Ψ s P Q q where
  toFun u := by
    by_cases h : FordTuplePairwiseDistinct u.1.1.1 ∧
        FordTuplePairwiseDistinct u.1.1.2
    · exact Sum.inl ⟨u, h⟩
    · exact Sum.inr ⟨u, not_and_or.mp h⟩
  invFun u := match u with
    | Sum.inl v => v.1
    | Sum.inr v => v.1
  left_inv u := by
    by_cases h : FordTuplePairwiseDistinct u.1.1.1 ∧
        FordTuplePairwiseDistinct u.1.1.2
    · simp [h]
    · simp [h]
  right_inv u := by
    rcases u with u | u
    · simp [u.2]
    · have h : ¬ (FordTuplePairwiseDistinct u.1.1.1.1 ∧
          FordTuplePairwiseDistinct u.1.1.1.2) := by
        exact not_and_or.mpr u.2
      simp [h]

theorem fordK_count_eq_distinct_add_repeated
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    fordKCount Ψ s P Q q =
      Nat.card (FordKDistinctSolution Ψ s P Q q) +
        Nat.card (FordKRepeatedSolution Ψ s P Q q) := by
  calc
    fordKCount Ψ s P Q q = Nat.card (FordKSolution Ψ s P Q q) := by
      rw [Nat.card_eq_fintype_card]
      rfl
    _ = Nat.card (FordKDistinctSolution Ψ s P Q q ⊕
        FordKRepeatedSolution Ψ s P Q q) :=
      Nat.card_congr (fordKDistinctRepeatedEquiv Ψ)
    _ = _ := Nat.card_sum

#print axioms fordK_repeated_card_le_pair_sum
#print axioms fordK_count_eq_distinct_add_repeated

end

end GafniTao
