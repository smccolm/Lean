import Dubon2026.SourceOriginalPrimePowerStep

/-! DUB-17/18 -> numerical modular genus -> original prime-power j-map
degree. The original full field at the next prime-power level is exactly
the simple extension already proved to have degree p. Native relative
degree avoids any auxiliary scalar-tower assumption.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField PrimePowerNonmembership

theorem relfinrank_adjoin_union_singleton
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (x : LaurentSeries ℚ) :
    relfinrank F (IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {x})) =
      Module.finrank F (IntermediateField.adjoin F ({x} : Set (LaurentSeries ℚ))) := by
  have h : F ≤ IntermediateField.adjoin ℚ ((F : Set (LaurentSeries ℚ)) ∪ {x}) :=
    fun _ hx => subset_adjoin ℚ _ (Or.inl hx)
  have he : IntermediateField.adjoin F ((F : Set (LaurentSeries ℚ)) ∪ {x}) =
      IntermediateField.adjoin F ({x} : Set (LaurentSeries ℚ)) := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact (IntermediateField.adjoin F {x}).algebraMap_mem (⟨y, hy⟩ : F)
      · exact subset_adjoin F _ hy
    · exact IntermediateField.adjoin.mono F _ _ Set.subset_union_right
  rw [relfinrank_eq_finrank_of_le h, extendScalars_adjoin h, he]

theorem original_prime_power_field_succ (p : ℕ) [Fact p.Prime] (a : ℕ) :
    modularFunctionFieldFull (p ^ (a + 1)) = IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull (p ^ a) : Set (LaurentSeries ℚ)) ∪
        {qExpand ℚ (p ^ (a + 1)) jq}) := by
  rw [← chainField_one_eq_original_prime_power p (a + 1), chainField_succ,
    chainField_one_eq_original_prime_power, qExpand_congr (pow_succ p a).symm jq]

theorem original_prime_power_fields_mono (p : ℕ) [Fact p.Prime] (a : ℕ) :
    modularFunctionFieldFull (p ^ a) ≤ modularFunctionFieldFull (p ^ (a + 1)) := by
  rw [← chainField_one_eq_original_prime_power p a,
    ← chainField_one_eq_original_prime_power p (a + 1)]
  exact chainField_mono 1 p a

theorem original_prime_power_step_relfinrank (p : ℕ) [Fact p.Prime] (k : ℕ) :
    relfinrank (modularFunctionFieldFull (p ^ (k + 1)))
      (modularFunctionFieldFull (p ^ (k + 2))) = p := by
  rw [original_prime_power_field_succ p (k + 1), relfinrank_adjoin_union_singleton]
  exact original_prime_power_step_finrank_eq p k

end
end Dubon2026.SourceFunctionField
