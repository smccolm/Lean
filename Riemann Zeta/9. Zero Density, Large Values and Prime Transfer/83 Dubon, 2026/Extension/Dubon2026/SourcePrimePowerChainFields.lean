import Dubon2026.SourcePrimeTwistedEmbedding

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> next-series nonmembership -> induction through the actual prime-power
adjoin tower over an original divisor field. These are the literal fields
used in the source's root-spreading argument, with their zero and successor
stages identified. No nonmembership or field-generation conclusion is assumed.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open IntermediateField PrimeDegreeAux

/-- The actual field obtained by adjoining the prime-power j series through stage i. -/
def chainField (M p : ℕ) [NeZero p] (i : ℕ) :
    IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ ((modularFunctionFieldFull M : Set (LaurentSeries ℚ)) ∪
    {x : LaurentSeries ℚ | ∃ j : ℕ, j ≤ i ∧ x = qExpand ℚ (p ^ j) jq})

theorem mem_chainField (M p : ℕ) [NeZero p] {j i : ℕ} (hj : j ≤ i) :
    qExpand ℚ (p ^ j) jq ∈ chainField M p i :=
  subset_adjoin ℚ _ (Or.inr ⟨j, hj, rfl⟩)

theorem full_le_chainField (M p : ℕ) [NeZero p] (i : ℕ) :
    modularFunctionFieldFull M ≤ chainField M p i :=
  fun _ hx => subset_adjoin ℚ _ (Or.inl hx)

theorem chainField_zero (M p : ℕ) [NeZero p] : chainField M p 0 = modularFunctionFieldFull M := by
  apply le_antisymm
  · rw [chainField, adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact hx
    · have hj0 : j = 0 := Nat.le_zero.mp hj
      subst j
      rw [qExpand_congr (pow_zero p) jq, qExpand_one_apply]
      exact jq_mem_full M
  · exact full_le_chainField M p 0

theorem chainField_mono (M p : ℕ) [NeZero p] (i : ℕ) :
    chainField M p i ≤ chainField M p (i + 1) := by
  rw [chainField, chainField]
  refine IntermediateField.adjoin.mono ℚ _ _ (Set.union_subset_union_right _ ?_)
  rintro z ⟨j, hj, rfl⟩
  exact ⟨j, le_trans hj (Nat.le_succ i), rfl⟩

theorem chainField_succ (M p : ℕ) [NeZero p] (i : ℕ) :
    chainField M p (i + 1) = IntermediateField.adjoin ℚ
      ((chainField M p i : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ (p ^ i * p) jq}) := by
  apply le_antisymm
  · rw [chainField, adjoin_le_iff]
    rintro x (hx | ⟨j, hj, rfl⟩)
    · exact subset_adjoin ℚ _ (Or.inl (full_le_chainField M p i hx))
    · rcases Nat.lt_or_ge j (i + 1) with h | h
      · exact subset_adjoin ℚ _ (Or.inl (mem_chainField M p (Nat.lt_succ_iff.mp h)))
      · have hje : j = i + 1 := le_antisymm hj h
        subst j
        refine subset_adjoin ℚ _ (Or.inr ?_)
        rw [Set.mem_singleton_iff]
        exact qExpand_congr (pow_succ p i) jq
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact chainField_mono M p i hx
    · rw [Set.mem_singleton_iff] at hx
      subst x
      rw [qExpand_congr (pow_succ p i).symm jq]
      exact mem_chainField M p (le_refl (i + 1))

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
