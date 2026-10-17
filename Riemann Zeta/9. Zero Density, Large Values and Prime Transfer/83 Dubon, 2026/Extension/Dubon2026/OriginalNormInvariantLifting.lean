import Dubon2026.OriginalCoinducedInvariantNorms

/-! # Invariant lifting through actual surjective coefficient maps

If an invariant in the original quotient is a literal norm, lift its
norm preimage and take the norm upstairs. This is the invariant-lifting
step for the actual fundamental coefficient's free presentation on
DUB-17's lattice/internal-Hom duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- A genuine surjective coefficient map lifts invariants when the original target has literal invariant norm preimages. -/
theorem originalInvariant_lift_of_norm_preimages
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    {A B : Rep k G} (f : A ⟶ B) (hf : Function.Surjective f.hom)
    (hB : ∀ x : B, x ∈ B.ρ.invariants → ∃ y : B, B.ρ.norm y = x)
    (x : B) (hx : x ∈ B.ρ.invariants) :
    ∃ y : A, y ∈ A.ρ.invariants ∧ f.hom y = x := by
  obtain ⟨z, hz⟩ := hB x hx
  obtain ⟨w, hw⟩ := hf z
  refine ⟨A.ρ.norm w, fun g => Representation.self_norm_apply A.ρ g w, ?_⟩
  rw [originalCoefficientMorphism_norm, hw, hz]

end
end Dubon2026
