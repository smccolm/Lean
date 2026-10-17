import Dubon2026.OriginalSPlaceFullClassImage
import Dubon2026.OriginalClassOutsideH2TowerSquare
import Dubon2026.OriginalVerticalIdeleClassInflation

/-! # Retain the source-induced full idele at the common comparison field

This composes the already proved source projection, outside-unit quotient
square and vertical idele/class square. It supplies the actual idele input
for the canonical total in the common-field scalar obstruction comparison;
no arbitrary class-to-idele lifting is used.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

/-- The inflated source S-place class is the outside-unit quotient of its
specified full-idele class at the same upper field. -/
theorem originalSPlaceFullIdele_H2_class_tower_comparison
    (K E M : Type) [Field K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (T : Finset (HeightOneSpectrum (𝓞 M)))
    (hS : ∀ (σ : Gal(E/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ S)
    (hT : ∀ (σ : Gal(M/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K M σ v ∈ T)
    (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E M w ∈ S)
    (x : groupCohomology (supportedUnrestrictedUnitRep K E S hS) 2) :
    groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(M/K) →* Gal(E/K))
      (originalClassesModOutsideBaseChangeRepHom K E M S T hS hT hST) 2
      ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalSPlaceClassComparison K E S hS)
        ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalSPlaceIdeleClassRepHom K E S hS) x)) =
    (groupCohomology.functor ℤ Gal(M/K) 2).map (originalIdeleClassesModOutsideRepHom K M T hT)
      ((groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M)
        (originalFullIdeleBaseChangeH2 K K E M
          ((groupCohomology.functor ℤ Gal(E/K) 2).map (originalSPlaceFullIdeleInclusion K E S hS) x))) := by
  let u := (groupCohomology.functor ℤ Gal(E/K) 2).map (originalSPlaceFullIdeleInclusion K E S hS) x
  let c := (groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) u
  have hsource := congrArg
    (groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(M/K) →* Gal(E/K))
      (originalClassesModOutsideBaseChangeRepHom K E M S T hS hT hST) 2)
    (originalSPlaceFullIdele_H2_class_comparison K E S hS x)
  have hsquare := originalClassOutsideH2_tower_square K E M S T hS hT hST c
  have hvert := congrArg
    ((groupCohomology.functor ℤ Gal(M/K) 2).map (originalIdeleClassesModOutsideRepHom K M T hT))
    (originalFullIdeleBaseChangeH2_vertical_class K E M u)
  exact hsource.trans (hsquare.trans hvert.symm)

end
end Dubon2026
