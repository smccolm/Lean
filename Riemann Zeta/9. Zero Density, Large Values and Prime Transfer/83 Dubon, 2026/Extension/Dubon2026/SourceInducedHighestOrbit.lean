import Dubon2026.SourceInducedGroupIrreducible

/-! Generation by the actual source highest vector under the original group.
The span is formed from actual right translates in the original induced
module. Its stability and nonzeroness are derived, then original group
irreducibility identifies it with the whole module.
-/

namespace Dubon2026
noncomputable section

universe u
variable (K : Type u) [Field K]

/-- A nonzero vector in an irreducible representation spans the whole module through its actual group orbit. This separates the orbit argument from the large source coordinate carrier. -/
theorem sourceRepresentation_nonzero_orbitSpan_eq_top
    {G V : Type*} [Monoid G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) [Representation.IsIrreducible ρ]
    (v : V) (hv0 : v ≠ 0) :
    Submodule.span K (Set.range fun g : G => ρ g v) = ⊤ := by
  let W := Submodule.span K (Set.range fun g => ρ g v)
  have hW (g : G) : ∀ p ∈ W, ρ g p ∈ W := by
    have hs : W ≤ W.comap (ρ g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨h, rfl⟩
      change ρ g (ρ h v) ∈ W
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    intro p hp
    exact hs hp
  have hv : v ∈ W := by
    have hm : ρ 1 v ∈ W := Submodule.subset_span ⟨1, rfl⟩
    simpa using hm
  let U : Subrepresentation ρ :=
    ⟨W, fun g {p} hp => hW g p hp⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
  · have he : W = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [he, Submodule.mem_bot] at hv
    exact (hv0 hv).elim
  · exact congrArg Subrepresentation.toSubmodule h

variable [CharZero K]
variable {m : ℕ} (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)

/-- The actual normalized highest vector generates the entire original source coefficient representation under its original general-linear group action. -/
theorem sourceInduced_highest_groupSpan :
    Submodule.span K (Set.range fun g : Matrix.GeneralLinearGroup (Fin (m + 1)) K =>
      generalLinearIntegralInducedRepresentation K (m + 1) weight g
        (integralDominantHighestVector K weight hw)) = ⊤ := by
  letI := sourceInduced_isIrreducible K weight hw
  exact sourceRepresentation_nonzero_orbitSpan_eq_top K
    (generalLinearIntegralInducedRepresentation K (m + 1) weight)
    (integralDominantHighestVector K weight hw)
    (integralDominantHighestVector_ne_zero K weight hw)

end
end Dubon2026
