import Dubon2026.SourceOriginalDivisorGeneration

/-! DUB-17/18 -> numerical modular genus -> joint original degree and
generation induction. Generation at N follows from generation and exact
degree only at its proper divisors. Lower-level conjugate products give
the concrete prime-predecessor membership; all divisor generators then
descend. The current-level degree is not an input to this generation step.
The subsequent degree step is still needed to close the joint induction.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots SourceLevelProjective
open scoped IntermediateField

theorem original_generation_of_proper_divisor_induction (N : ℕ) [NeZero N]
    (hproper : ∀ (d : ℕ), d ∣ N → d < N → ∀ [NeZero d],
      modularFunctionFieldFull d = IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) ∧
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull d) = dedekindPsi d) :
    modularFunctionFieldFull N = IntermediateField.adjoin ℚ
      ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) := by
  apply original_full_eq_pair_of_predecessor_membership N
  · intro M _ p hp hMp
    haveI : Fact p.Prime := ⟨hp⟩
    have hMlt : M < N := by
      rw [← hMp]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
    have hMN : M ∣ N := ⟨p, hMp.symm⟩
    let K := AlgebraicClosure ℚ
    haveI : NeZero (M : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne M)⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
    have hu := hz.isUnit (NeZero.ne M)
    have hζ : IsPrimitiveRoot (hu.unit : K) M := by rw [hu.unit_spec]; exact hz
    have hproduct := expandedJMinpoly_eq_slotProduct_of_divisor_induction
      M hu.unit hζ (fun e he _ => hproper e (he.trans hMN)
        (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) he) hMlt))
    have hmem := original_predecessor_mem_pair_of_lower_product M p hu.unit hproduct
    simpa only [hMp] using hmem
  · intro M _ p hp hMp
    have hMlt : M < N := by
      rw [← hMp]
      exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
    exact (hproper M ⟨p, hMp.symm⟩ hMlt).1

end
end Dubon2026.SourceFunctionField
