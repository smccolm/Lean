import Dubon2026.OriginalCanonicalClassSystem

/-! # Detect the actual class kernel with the canonical total

Consume the complete original invariant system. Its injectivity and
literal idele-total formula characterize the class-map kernel, providing
a semantic consumer of DUB-17's canonical normalization construction.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- An actual canonical class system identifies zero class projection exactly with zero canonical total. -/
theorem originalIdeleClass_canonical_system_zero_iff
    (K E : Type) [Field K] [Field E] [NumberField E] [Algebra K E]
    (total : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (h : OriginalCanonicalClassInvariantSystem K E total) :
    ∀ x : groupCohomology (originalFullIdeleRep K E) 2,
      (groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x = 0 ↔
        total x = 0 := by
  obtain ⟨invG, hi, _, ht, _⟩ := h
  intro x
  constructor
  · intro hx
    rw [← ht x, hx]
    exact map_zero invG
  · intro hx
    apply hi
    exact (ht x).trans (hx.trans (map_zero invG).symm)

end
end Dubon2026
