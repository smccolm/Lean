import Dubon2026.SourceResidueRelativeDegree
import Dubon2026.SourceModularRelationsInResidueCharacteristic

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate embeddings.
The actual integral monic relations supply the j-substitution minimal
polynomials in residue characteristic. The simple/full degree comparison
has the explicit lower-level generation input used by the joint induction.
Adapted from the existing local SourceOriginalJMinimalPolynomial proof. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField

theorem residue_j_substitution_isIntegral (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral K⟮jqModC K⟯ (qExpand K N (jqModC K)) := by
  obtain ⟨P, hm, hr⟩ := exists_monic_relation_coeff N K
  exact integral_of_relationAtSeed_root _ P hm (IntermediateField.mem_adjoin_simple_self K _) hr

theorem residue_j_simple_finrank_eq_minpoly (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Module.finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮qExpand K N (jqModC K)⟯ =
      (minpoly K⟮jqModC K⟯ (qExpand K N (jqModC K))).natDegree :=
  IntermediateField.adjoin.finrank (residue_j_substitution_isIntegral K N)

theorem residue_j_adjoin_union_eq_pair (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IntermediateField.adjoin K ((K⟮jqModC K⟯ : Set (LaurentSeries K)) ∪ {qExpand K N (jqModC K)}) =
      IntermediateField.adjoin K ({jqModC K, qExpand K N (jqModC K)} : Set (LaurentSeries K)) := by
  apply le_antisymm
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact (IntermediateField.adjoin.mono K _ _ (by intro y hy; exact Or.inl hy)) hx
    · exact subset_adjoin K _ (Or.inr hx)
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact subset_adjoin K _ (Or.inl (hx ▸ IntermediateField.mem_adjoin_simple_self K (jqModC K)))
    · exact subset_adjoin K _ (Or.inr hx)

theorem residue_minpoly_degree_eq_full_relfinrank_of_generation
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (hgen : modularFunctionFieldCoeff N K =
      IntermediateField.adjoin K ({jqModC K, qExpand K N (jqModC K)} : Set (LaurentSeries K))) :
    (minpoly K⟮jqModC K⟯ (qExpand K N (jqModC K))).natDegree =
      relfinrank K⟮jqModC K⟯ (modularFunctionFieldCoeff N K) := by
  rw [hgen, ← residue_j_adjoin_union_eq_pair, coefficient_relfinrank_adjoin_union_singleton]
  exact (residue_j_simple_finrank_eq_minpoly K N).symm

end
end Dubon2026.SourceFunctionField
