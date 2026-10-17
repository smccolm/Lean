import Dubon2026.OriginalSPlaceClassComparison
import Dubon2026.OriginalIdeleUnrestrictedCoordinates

/-! # The actual full-idele representative of an S-place class image

Embed the source local product with outside coordinates equal to one.
Its image in full classes modulo outside units is the original S-place
class comparison. This retains a specific full-idele H2 input for the
normalized local pairing comparison in DUB-17.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Include the actual S-place product in full ideles with unit outside coordinates. -/
def originalSPlaceFullIdeleInclusion :
    supportedUnrestrictedUnitRep K L S hS ⟶ originalFullIdeleRep K L :=
  originalSPlaceSupportedInclusion K L S hS ≫ originalSupportedFullIdeleInclusion K L S hS

/-- The original source-class comparison retains precisely this full-idele representative. -/
theorem originalSPlaceFullIdele_class_comparison :
    originalSPlaceIdeleClassRepHom K L S hS ≫ originalSPlaceClassComparison K L S hS =
      originalSPlaceFullIdeleInclusion K L S hS ≫ originalFullClassRepHom K L ≫
        originalIdeleClassesModOutsideRepHom K L S hS := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- The actual source-induced class H2 image comes from its specified full-idele H2 class. -/
theorem originalSPlaceFullIdele_H2_class_comparison
    (x : groupCohomology (supportedUnrestrictedUnitRep K L S hS) 2) :
    (groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceClassComparison K L S hS)
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceIdeleClassRepHom K L S hS) x) =
    (groupCohomology.functor ℤ Gal(L/K) 2).map (originalIdeleClassesModOutsideRepHom K L S hS)
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS) x)) := by
  have h := congrArg (fun f => (groupCohomology.functor ℤ Gal(L/K) 2).map f)
    (originalSPlaceFullIdele_class_comparison K L S hS)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun f => f x) h

end
end Dubon2026
