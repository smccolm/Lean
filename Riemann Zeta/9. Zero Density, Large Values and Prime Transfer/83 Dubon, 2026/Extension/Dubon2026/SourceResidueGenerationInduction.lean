import Dubon2026.SourceResidueDivisorGeneration

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> joint generation/degree induction. Adapt local SourceOriginalGenerationInduction
to the actual coefficient-field divisor field. Lower-level conjugate products
force a unique common root of the prime relation and minimal polynomial;
native descent recovers the preceding j series. Proper-divisor induction
inputs remain explicit; the current-level degree is not assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem residue_generation_of_proper_divisor_induction (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (hproper : ∀ (d : ℕ), d ∣ N → d < N → ∀ [NeZero d],
      modularFunctionFieldCoeff d K = IntermediateField.adjoin K
        ({(jqModC K), qExpand K d (jqModC K)} : Set (LaurentSeries K)) ∧
      relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff d K) = dedekindPsi d) :
    modularFunctionFieldCoeff N K = IntermediateField.adjoin K
      ({(jqModC K), qExpand K N (jqModC K)} : Set (LaurentSeries K)) := by
  apply residue_full_eq_pair_of_predecessor_membership N
  · intro M _ p hp hMp
    haveI : Fact p.Prime := ⟨hp⟩
    have hMlt : M < N := by
      rw [← hMp]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
    have hMN : M ∣ N := ⟨p, hMp.symm⟩
    haveI : NeZero (M : K) := ⟨ne_zero_of_dvd_ne_zero hNK hMN.natCast⟩
    have hpK : (p : K) ≠ 0 := ne_zero_of_dvd_ne_zero hNK
      (show p ∣ N from ⟨M, by rw [← hMp, Nat.mul_comm]⟩).natCast
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
    have hu := hz.isUnit (NeZero.ne M)
    have hζ : IsPrimitiveRoot (hu.unit : K) M := by rw [hu.unit_spec]; exact hz
    have hproduct := residueExpandedJMinpoly_eq_slotProduct_of_divisor_induction
      M hu.unit hζ (fun e he _ => hproper e (he.trans hMN)
        (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) he) hMlt))
    have hmem := residue_predecessor_mem_pair_of_lower_product M p hpK hu.unit hproduct
    simpa only [hMp] using hmem
  · intro M _ p hp hMp
    have hMlt : M < N := by
      rw [← hMp]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
    exact (hproper M ⟨p, hMp.symm⟩ hMlt).1

end
end Dubon2026.SourceFunctionField
