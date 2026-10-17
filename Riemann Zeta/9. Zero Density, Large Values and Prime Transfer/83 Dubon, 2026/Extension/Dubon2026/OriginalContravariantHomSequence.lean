import Dubon2026.OriginalInternalHomPrecomposition

/-! # Literal dualization of the original coefficient sequence

The actual precomposition maps reverse a coefficient short complex.
This supplies the relation-presentation dual sequence used to apply the
existing continuous cup/connecting adjunction on DUB-17's source-duality
route. Exactness is a separate obligation.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G : Type} [Group G] (X : ShortComplex (Rep.{0} ℤ G)) (C : Rep.{0} ℤ G)

/-- The actual reversed internal-Hom sequence, with literal precomposition maps. -/
abbrev originalContravariantHomShortComplex : ShortComplex (Rep ℤ G) where
  X₁ := (Rep.ihom X.X₃).obj C
  X₂ := (Rep.ihom X.X₂).obj C
  X₃ := (Rep.ihom X.X₁).obj C
  f := originalInternalHomPrecomposition C X.g
  g := originalInternalHomPrecomposition C X.f
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro η
    change X.X₃ →ₗ[ℤ] C at η
    apply LinearMap.ext
    intro x
    change η (X.g.hom (X.f.hom x)) = 0
    have hz := congrArg (fun f : X.X₁ ⟶ X.X₃ => f.hom x) X.zero
    change X.g.hom (X.f.hom x) = 0 at hz
    rw [hz, map_zero]

end
end Dubon2026
