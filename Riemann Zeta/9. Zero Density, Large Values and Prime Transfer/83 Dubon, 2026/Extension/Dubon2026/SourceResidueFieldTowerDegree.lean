import Dubon2026.SourceResidueRelativeRootTransfer
import Dubon2026.SourceLevelPsiPrimeStep

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
Adapt local SourceOriginalFieldTowerDegree to the actual coefficient-field j series and divisor field.
The same native minimal-polynomial, tower and primitive-slot arguments are used.
Every lower-level generation, degree and product hypothesis remains explicit;
the all-level consumer must derive them by induction. No new characteristic-zero
structure is imposed on the residue coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_full_eq_adjoin_over_divisor_of_generation
    (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (hgen : modularFunctionFieldCoeff N K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K))) :
    modularFunctionFieldCoeff N K = IntermediateField.adjoin K
      ((modularFunctionFieldCoeff M K : Set (LaurentSeries K)) ∪ {qExpand K N (jqModC K)}) := by
  apply le_antisymm
  · rw [hgen, adjoin_le_iff]
    rintro x (rfl | hx)
    · exact subset_adjoin K _ (Or.inl (jq_mem_coeff_field M K))
    · exact subset_adjoin K _ (Or.inr hx)
  · rw [adjoin_le_iff]
    rintro x (hx | rfl)
    · exact coefficient_field_mono hMN hx
    · exact jqd_mem_coeff_field N K dvd_rfl

theorem residue_j_substitution_isIntegral_over_full (M N : ℕ) [NeZero N] :
    IsIntegral (modularFunctionFieldCoeff M K) (qExpand K N (jqModC K)) := by
  obtain ⟨P, hm, hr⟩ := exists_monic_relation_coeff N K
  exact integral_of_relationAtSeed_root _ P hm (jq_mem_coeff_field M K) hr


theorem residue_relative_minpoly_degree_mul (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (hgen : modularFunctionFieldCoeff N K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K))) :
    (minpoly (modularFunctionFieldCoeff M K) (qExpand K N (jqModC K))).natDegree *
      relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff M K) =
      relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff N K) := by
  have hj : K⟮(jqModC K)⟯ ≤ modularFunctionFieldCoeff M K :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_coeff_field M K))
  have h := relfinrank_mul_relfinrank hj (coefficient_field_mono hMN)
  have hstep : relfinrank (modularFunctionFieldCoeff M K) (modularFunctionFieldCoeff N K) =
      (minpoly (modularFunctionFieldCoeff M K) (qExpand K N (jqModC K))).natDegree := by
    rw [residue_full_eq_adjoin_over_divisor_of_generation M N hMN hgen,
      coefficient_relfinrank_adjoin_union_singleton]
    exact IntermediateField.adjoin.finrank (residue_j_substitution_isIntegral_over_full M N)
  rw [hstep, Nat.mul_comm] at h
  exact h

theorem residue_relative_prime_minpoly_degree_of_induction
    (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (hgen : modularFunctionFieldCoeff (M * p) K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K (M * p) (jqModC K)} : Set (LaurentSeries K)))
    (hM : relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff M K) = dedekindPsi M)
    (hMp : relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff (M * p) K) = dedekindPsi (M * p)) :
    (minpoly (modularFunctionFieldCoeff M K) (qExpand K (M * p) (jqModC K))).natDegree =
      if p ∣ M then p else p + 1 := by
  have h := residue_relative_minpoly_degree_mul M (M * p) (dvd_mul_right M p) hgen
  rw [hM, hMp] at h
  split_ifs with hpM
  · rw [dedekindPsi_mul_prime_dvd (NeZero.ne M) hp.out hpM, Nat.mul_comm (dedekindPsi M) p] at h
    exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos (NeZero.ne M)) h
  · rw [dedekindPsi_mul_prime_not_dvd hp.out hpM, Nat.mul_comm (dedekindPsi M) (p + 1)] at h
    exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos (NeZero.ne M)) h

end
end Dubon2026.SourceFunctionField
