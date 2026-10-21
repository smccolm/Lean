import Dubon2026.SourceOriginalRelativeRootTransfer
import Dubon2026.SourceLevelPsiPrimeStep

/-! DUB-17/18 -> numerical modular genus -> composite degree -> actual
relative minimal-polynomial degree in the conjugate induction. The
original divisor field inclusions, derived integrality and native relative
degree multiplication turn the induction's generation and absolute-degree
data into the precise prime-step input. These induction data remain explicit.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField

theorem original_full_mono_of_dvd {M N : ℕ} (hMN : M ∣ N) :
    modularFunctionFieldFull M ≤ modularFunctionFieldFull N := by
  apply IntermediateField.adjoin.mono
  rintro x ⟨d, hd, hdM, rfl⟩
  exact ⟨d, hd, hdM.trans hMN, rfl⟩

theorem original_full_eq_adjoin_over_divisor_of_generation
    (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (hgen : modularFunctionFieldFull N =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ))) :
    modularFunctionFieldFull N = IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull M : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ N jq}) := by
  apply le_antisymm
  · rw [hgen, adjoin_le_iff]
    rintro x (rfl | hx)
    · exact subset_adjoin ℚ _ (Or.inl (jq_mem_full M))
    · exact subset_adjoin ℚ _ (Or.inr hx)
  · rw [adjoin_le_iff]
    rintro x (hx | rfl)
    · exact original_full_mono_of_dvd hMN hx
    · exact jqd_mem_full N dvd_rfl

theorem original_j_substitution_isIntegral_over_full (M N : ℕ) [NeZero N] :
    IsIntegral (modularFunctionFieldFull M) (qExpand ℚ N jq) := by
  obtain ⟨P, hm, hr⟩ := exists_monic_relation N
  let j : modularFunctionFieldFull M := ⟨jq, jq_mem_full M⟩
  refine ⟨relationAtSeed P j, hm.map _, ?_⟩
  rw [← Polynomial.eval_map, relationAtSeed_map]
  exact relationAtSeed_jq_eval P hr

theorem original_relative_minpoly_degree_mul (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (hgen : modularFunctionFieldFull N =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ))) :
    (minpoly (modularFunctionFieldFull M) (qExpand ℚ N jq)).natDegree *
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull M) =
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull N) := by
  have hj : ℚ⟮jq⟯ ≤ modularFunctionFieldFull M :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_full M))
  have h := relfinrank_mul_relfinrank hj (original_full_mono_of_dvd hMN)
  have hstep : relfinrank (modularFunctionFieldFull M) (modularFunctionFieldFull N) =
      (minpoly (modularFunctionFieldFull M) (qExpand ℚ N jq)).natDegree := by
    rw [original_full_eq_adjoin_over_divisor_of_generation M N hMN hgen,
      relfinrank_adjoin_union_singleton]
    exact IntermediateField.adjoin.finrank (original_j_substitution_isIntegral_over_full M N)
  rw [hstep, Nat.mul_comm] at h
  exact h

theorem original_relative_prime_minpoly_degree_of_induction
    (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (hgen : modularFunctionFieldFull (M * p) =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ (M * p) jq} : Set (LaurentSeries ℚ)))
    (hM : relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull M) = dedekindPsi M)
    (hMp : relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull (M * p)) = dedekindPsi (M * p)) :
    (minpoly (modularFunctionFieldFull M) (qExpand ℚ (M * p) jq)).natDegree =
      if p ∣ M then p else p + 1 := by
  have h := original_relative_minpoly_degree_mul M (M * p) (dvd_mul_right M p) hgen
  rw [hM, hMp] at h
  split_ifs with hpM
  · rw [dedekindPsi_mul_prime_dvd (NeZero.ne M) hp.out hpM, Nat.mul_comm (dedekindPsi M) p] at h
    exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos (NeZero.ne M)) h
  · rw [dedekindPsi_mul_prime_not_dvd hp.out hpM, Nat.mul_comm (dedekindPsi M) (p + 1)] at h
    exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos (NeZero.ne M)) h

end
end Dubon2026.SourceFunctionField
