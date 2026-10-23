import Dubon2026.SourceResiduePredecessorGeneration

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> joint generation/degree induction. Adapt local SourceOriginalDivisorGeneration
to the actual coefficient-field divisor field. Lower-level conjugate products
force a unique common root of the prime relation and minimal polynomial;
native descent recovers the preceding j series. Proper-divisor induction
inputs remain explicit; the current-level degree is not assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
variable {K : Type*} [Field K]

theorem residue_full_eq_pair_of_predecessor_membership (N : ℕ) [NeZero N]
    (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      qExpand K M (jqModC K) ∈ IntermediateField.adjoin K
        ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)))
    (hgen : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      modularFunctionFieldCoeff M K = IntermediateField.adjoin K
        ({(jqModC K), qExpand K M (jqModC K)} : Set (LaurentSeries K))) :
    modularFunctionFieldCoeff N K = IntermediateField.adjoin K
      ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)) := by
  apply le_antisymm
  · rw [modularFunctionFieldCoeff, IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hd0, hdN, rfl⟩
    by_cases hd : d = N
    · subst d
      exact IntermediateField.subset_adjoin K _ (Or.inr rfl)
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
      have hsub : modularFunctionFieldCoeff (d * v) K ≤ IntermediateField.adjoin K
          ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)) := by
        rw [hgen (d * v) u.minFac hp hN, IntermediateField.adjoin_le_iff]
        rintro y (rfl | hy)
        · exact IntermediateField.subset_adjoin K _ (Or.inl rfl)
        · rw [Set.mem_singleton_iff] at hy
          exact hy ▸ hmem
      exact hsub (jqd_mem_coeff_field (d * v) K (dvd_mul_right d v))
  · rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | hy)
    · exact jq_mem_coeff_field N K
    · rw [Set.mem_singleton_iff] at hy
      exact hy ▸ jqd_mem_coeff_field N K dvd_rfl

end
end Dubon2026.SourceFunctionField
