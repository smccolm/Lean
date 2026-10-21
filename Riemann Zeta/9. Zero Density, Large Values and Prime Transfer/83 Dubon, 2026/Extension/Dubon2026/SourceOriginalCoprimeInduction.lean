import Dubon2026.SourceOriginalCoprimeNonmembership

/-! DUB-17/18 -> numerical modular genus -> joint all-level degree and
generation induction. The divisor-level induction hypotheses supply the
actual lower conjugate identity over the native rational algebraic
closure, hence j_p is outside the original level-M field when p does
not divide M. This is the base nonmembership input to the already proved
prime-power spread argument over that original level-M field.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField

theorem prime_j_not_mem_original_coprime_of_divisor_induction (M p : ℕ)
    [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (hall : ∀ (d : ℕ), d ∣ M → ∀ [NeZero d],
      modularFunctionFieldFull d = IntermediateField.adjoin ℚ
        ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) ∧
      relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull d) = dedekindPsi d) :
    qExpand ℚ p jq ∉ modularFunctionFieldFull M := by
  let K := AlgebraicClosure ℚ
  haveI : NeZero (M : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne M)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  have hu := hz.isUnit (NeZero.ne M)
  have hζ : IsPrimitiveRoot (hu.unit : K) M := by rw [hu.unit_spec]; exact hz
  have hproduct := expandedJMinpoly_eq_slotProduct_of_divisor_induction M hu.unit hζ hall
  exact prime_j_not_mem_original_coprime_of_conjugate_product M p hpM hu.unit hζ
    (hall M dvd_rfl).1 hproduct

end
end Dubon2026.SourceFunctionField
