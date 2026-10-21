import Dubon2026.SourceOriginalDegreeBaseChange
import Dubon2026.SourcePrimePowerRelativeStep

/-! DUB-17/18 -> numerical modular genus -> exact composite j-map degree
-> explicit roots of the original minimal polynomial. The original monic
relations already prove integrality, so no new finiteness premise is needed.
This module records that direct reuse and relates the actual simple-field
degree to the full-field degree when their generation equality is available.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField

theorem original_j_substitution_isIntegral (N : ℕ) [NeZero N] :
    IsIntegral ℚ⟮jq⟯ (qExpand ℚ N jq) := by
  obtain ⟨P, hm, hr⟩ := exists_monic_relation N
  let j : ℚ⟮jq⟯ := ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩
  refine ⟨relationAtSeed P j, hm.map _, ?_⟩
  rw [← Polynomial.eval_map, relationAtSeed_map]
  exact relationAtSeed_jq_eval P hr

theorem original_j_simple_finrank_eq_minpoly (N : ℕ) [NeZero N] :
    Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮qExpand ℚ N jq⟯ =
      (minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).natDegree :=
  IntermediateField.adjoin.finrank (original_j_substitution_isIntegral N)

theorem original_j_adjoin_union_eq_pair (N : ℕ) [NeZero N] :
    IntermediateField.adjoin ℚ ((ℚ⟮jq⟯ : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ N jq}) =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) := by
  apply le_antisymm
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact (IntermediateField.adjoin.mono ℚ _ _ (by intro y hy; exact Or.inl hy)) hx
    · exact subset_adjoin ℚ _ (Or.inr hx)
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact subset_adjoin ℚ _ (Or.inl (hx ▸ IntermediateField.mem_adjoin_simple_self ℚ jq))
    · exact subset_adjoin ℚ _ (Or.inr hx)

theorem original_minpoly_degree_eq_full_relfinrank_of_generation
    (N : ℕ) [NeZero N]
    (hgen : modularFunctionFieldFull N =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ))) :
    (minpoly ℚ⟮jq⟯ (qExpand ℚ N jq)).natDegree =
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull N) := by
  rw [hgen, ← original_j_adjoin_union_eq_pair, relfinrank_adjoin_union_singleton]
  exact (original_j_simple_finrank_eq_minpoly N).symm

end
end Dubon2026.SourceFunctionField
