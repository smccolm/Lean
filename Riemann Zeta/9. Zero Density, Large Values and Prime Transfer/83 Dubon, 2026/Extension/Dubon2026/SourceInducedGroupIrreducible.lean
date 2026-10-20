import Dubon2026.SourceInducedGroupLieStability
import Mathlib.RepresentationTheory.Irreducible

/-! Irreducibility for the original source general-linear representation.
The original group action supplies its own differential stability. Thus the
proved Lie irreducibility applies to its actual invariant subspaces, and the
explicit nonzero highest vector supplies the nontriviality requirement.
-/

namespace Dubon2026
noncomputable section

universe u
variable (K : Type u) [Field K] [CharZero K]
variable {m : ℕ} (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)

include hw in
/-- Every invariant subspace of the original source general-linear representation is zero or the entire original coefficient module. -/
theorem sourceInduced_group_submodule_eq_bot_or_top
    (W : Submodule K (generalLinearIntegralInducedSubmodule K (m + 1) weight))
    (hW : ∀ g : Matrix.GeneralLinearGroup (Fin (m + 1)) K,
      ∀ p ∈ W, generalLinearIntegralInducedRepresentation K (m + 1) weight g p ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rcases sourceInduced_lieSubmodule_eq_bot_or_top K weight hw
      (sourceInducedGroupLieSubmodule K (m + 1) weight W hW) with h | h
  · exact Or.inl (congrArg LieSubmodule.toSubmodule h)
  · exact Or.inr (congrArg LieSubmodule.toSubmodule h)

include hw in
/-- The original source-induced general-linear representation is irreducible, including nontriviality, in Mathlib's representation-theoretic sense. -/
theorem sourceInduced_isIrreducible :
    Representation.IsIrreducible
      (generalLinearIntegralInducedRepresentation K (m + 1) weight) := by
  refine
    { exists_pair_ne := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    have he := congrArg Subrepresentation.toSubmodule h
    change (⊥ : Submodule K (generalLinearIntegralInducedSubmodule K (m + 1) weight)) = ⊤ at he
    have hv : integralDominantHighestVector K weight hw ∈
        (⊥ : Submodule K (generalLinearIntegralInducedSubmodule K (m + 1) weight)) := by
      rw [he]
      exact Submodule.mem_top
    exact integralDominantHighestVector_ne_zero K weight hw ((Submodule.mem_bot K).mp hv)
  · intro W
    rcases sourceInduced_group_submodule_eq_bot_or_top K weight hw W.toSubmodule
        (fun g p hp => W.apply_mem_toSubmodule g hp) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end
end Dubon2026
