import Dubon2026.SourceOriginalPredecessorGeneration

/-! DUB-17/18 -> numerical modular genus -> original all-level
generation. Every proper divisor lies in a maximal proper divisor M
with prime quotient N/M. Generation at M and the preceding-series
membership put its entire original field in Q(j,j_N). Thus the concrete
prime predecessor construction supplies all divisor generators; no
generic field-generation certificate replaces the actual j-series.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_div_mem_modularFunctionField.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField

theorem original_full_eq_pair_of_predecessor_membership (N : ℕ) [NeZero N]
    (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      qExpand ℚ M jq ∈ IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)))
    (hgen : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      modularFunctionFieldFull M = IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ M jq} : Set (LaurentSeries ℚ))) :
    modularFunctionFieldFull N = IntermediateField.adjoin ℚ
      ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) := by
  apply le_antisymm
  · rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hd0, hdN, rfl⟩
    by_cases hd : d = N
    · subst d
      exact IntermediateField.subset_adjoin ℚ _ (Or.inr rfl)
    · obtain ⟨u, hu⟩ := hdN
      have hu1 : u ≠ 1 := fun he => hd (by simpa only [he, mul_one] using hu.symm)
      have hu0 : u ≠ 0 := fun he => NeZero.ne N (by rw [hu, he, mul_zero])
      have hp : u.minFac.Prime := Nat.minFac_prime hu1
      obtain ⟨v, hv⟩ := Nat.minFac_dvd u
      have hv0 : v ≠ 0 := fun he => hu0 (by rw [hv, he, mul_zero])
      haveI : NeZero (d * v) := ⟨Nat.mul_ne_zero hd0.out hv0⟩
      have hN : (d * v) * u.minFac = N := by
        calc
          (d * v) * u.minFac = d * (u.minFac * v) := by ring
          _ = d * u := congrArg (d * ·) hv.symm
          _ = N := hu.symm
      have hmem := hstep (d * v) u.minFac hp hN
      have hsub : modularFunctionFieldFull (d * v) ≤ IntermediateField.adjoin ℚ
          ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) := by
        rw [hgen (d * v) u.minFac hp hN, IntermediateField.adjoin_le_iff]
        rintro y (rfl | hy)
        · exact IntermediateField.subset_adjoin ℚ _ (Or.inl rfl)
        · rw [Set.mem_singleton_iff] at hy
          exact hy ▸ hmem
      exact hsub (jqd_mem_full (d * v) (dvd_mul_right d v))
  · rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | hy)
    · exact jq_mem_full N
    · rw [Set.mem_singleton_iff] at hy
      exact hy ▸ jqd_mem_full N dvd_rfl

end
end Dubon2026.SourceFunctionField
