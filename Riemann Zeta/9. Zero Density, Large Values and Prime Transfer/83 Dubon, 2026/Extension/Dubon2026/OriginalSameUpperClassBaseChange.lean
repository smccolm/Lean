import Dubon2026.OriginalIdeleBaseChangeTower
import Dubon2026.OriginalFullIdeleBaseChangeH2
import Dubon2026.OriginalIdeleClassH2Restriction

/-! The same-upper-field comparison needed to apply the canonical
nonnormal total formula to the actual common-field Sylow restriction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- Actual idele base change along the identity field inclusion is the identity.
This follows from the already proved tower law and injectivity. -/
theorem originalIdeleBaseChangeMap_self (L : Type) [Field L] [NumberField L]
    (x : (NumberField.AdeleRing (𝓞 L) L)ˣ) : originalIdeleBaseChangeMap L L x = x := by
  apply originalIdeleBaseChangeMap_injective L L
  exact originalIdeleBaseChangeMap_tower L L L x

/-- The same identity holds on the actual idele-class quotient. -/
theorem originalIdeleClassBaseChangeMap_self (L : Type) [Field L] [NumberField L]
    (x : OriginalNumberFieldIdeleClassGroup L) : originalIdeleClassBaseChangeMap L L x = x := by
  induction x using QuotientGroup.induction_on
  rename_i x
  change originalIdeleClassBaseChangeMap L L (QuotientGroup.mk' (numberFieldPrincipalIdele L).range x) = _
  rw [originalIdeleClassBaseChangeMap_mk, originalIdeleBaseChangeMap_self]
  rfl

variable (K E M : Type) [Field K] [Field E] [Field M] [NumberField M]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M] [IsGalois K M]

/-- With the upper field unchanged, actual full-class base change is
precisely restriction along the displayed lower-field inclusion. -/
theorem originalFullClassBaseChangeH2_same_upper
    (x : groupCohomology (originalIdeleClassRep K M) 2) :
    groupCohomology.map (galoisBaseChangeRestriction K E M M)
      (originalFullClassFieldBaseChangeRepHom K E M M) 2 x =
      originalIdeleClassTowerH2Restriction K E M x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.H2π _ c) =
      groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    change Additive.ofMul (originalIdeleClassBaseChangeMap M M
      (c (galoisBaseChangeRestriction K E M M g.1,
        galoisBaseChangeRestriction K E M M g.2)).toMul) = _
    rw [originalIdeleClassBaseChangeMap_self]
    have hr (s : Gal(M/E)) : galoisBaseChangeRestriction K E M M s =
        galoisTowerBaseRestriction K E M s := by
      apply AlgEquiv.ext
      intro z
      exact galoisBaseChangeRestriction_commutes K E M M s z
    rw [hr, hr]
    rfl

/-- Projecting the original idele base change at the same upper field
gives the literal restriction of its original full-class image. -/
theorem originalFullIdeleBaseChangeH2_class_same_upper
    (x : groupCohomology (originalFullIdeleRep K M) 2) :
    (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      (originalFullIdeleBaseChangeH2 K E M M x) =
      originalIdeleClassTowerH2Restriction K E M
        ((groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M) x) :=
  (originalFullIdeleBaseChangeH2_class K E M M x).trans
    (originalFullClassBaseChangeH2_same_upper K E M _)

end
end Dubon2026
