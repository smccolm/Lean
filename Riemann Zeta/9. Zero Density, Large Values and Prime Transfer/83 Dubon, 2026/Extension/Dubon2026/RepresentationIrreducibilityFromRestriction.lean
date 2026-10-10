import Mathlib.RepresentationTheory.Irreducible

/-! # Actual original irreducibility passes from a restricted action to the whole action -/

namespace Dubon2026

variable {K G H V : Type*} [Field K] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module K V]

/-- Every actual invariant subspace of the whole representation is invariant under the original restricted action; irreducibility of that restriction therefore proves whole irreducibility. -/
theorem representation_irreducible_of_restriction (q : G →* H) (ρ : Representation K H V)
    [Representation.IsIrreducible (ρ.comp q)] : Representation.IsIrreducible ρ := by
  have htb : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    intro h
    apply top_ne_bot (α := Subrepresentation (ρ.comp q))
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun W : Subrepresentation ρ => W.toSubmodule) h
  letI : Nontrivial (Subrepresentation ρ) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  let Wq : Subrepresentation (ρ.comp q) :=
    ⟨W.toSubmodule, fun g _ hv => W.apply_mem_toSubmodule (q g) hv⟩
  rcases eq_bot_or_eq_top Wq with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp q) => U.toSubmodule) hb
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp q) => U.toSubmodule) ht

end Dubon2026
