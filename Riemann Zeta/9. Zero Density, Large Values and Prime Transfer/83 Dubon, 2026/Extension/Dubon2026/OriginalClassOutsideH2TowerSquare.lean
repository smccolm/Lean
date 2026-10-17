import Dubon2026.OriginalClassesModOutsideBaseChange
import Dubon2026.OriginalIdeleClassH2Inflation

/-! # Original full-class inflation commutes with the outside-unit quotient

The source cup and scalar obstruction are compared at a constructed common
finite arithmetic stage. This square is needed to transport that equality
to original full-class H2 and reflect zero through its proved injective
inflation, on DUB-17's local reciprocity and reverse localization chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(E/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E L w ∈ S)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The literal original full-class inflation and outside-unit quotient
commute on every genuine full-class H2 input. -/
theorem originalClassOutsideH2_tower_square
    (x : groupCohomology (originalIdeleClassRep K E) 2) :
    groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
      (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST) 2
      ((groupCohomology.functor ℤ Gal(E/K) 2).map
        (originalIdeleClassesModOutsideRepHom K E S hS) x) =
    (groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L T hT)
      (groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
        (originalIdeleClassTowerInclusion K E L) 2 x) := by
  induction x using groupCohomology.H2_induction_on with
  | _ c =>
    change groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
      (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST) 2
      (groupCohomology.map (MonoidHom.id Gal(E/K))
        (originalIdeleClassesModOutsideRepHom K E S hS) 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map (MonoidHom.id Gal(L/K))
        (originalIdeleClassesModOutsideRepHom K L T hT) 2
        (groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
          (originalIdeleClassTowerInclusion K E L) 2 (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext gh
    rfl

end
end Dubon2026
