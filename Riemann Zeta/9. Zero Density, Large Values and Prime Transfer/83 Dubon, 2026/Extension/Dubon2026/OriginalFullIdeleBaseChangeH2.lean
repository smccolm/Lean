import Dubon2026.OriginalFullIdeleCohomologySequence
import Dubon2026.OriginalIdeleRestrictScalars
import Dubon2026.GaloisUnitBaseChange
import Dubon2026.OriginalOutsideClassBaseChange

/-! # Actual full-idele and class H2 under a change of base

The literal idele embedding intertwines the actual field restriction.
Its H2 map commutes with both principal inclusion and class projection.
This is the map needed to compute the restriction of the constructed
auxiliary cyclic class in DUB-17's generator-transfer argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable (K E L M : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L]

/-- Actual idele inclusion with the genuine base-change Galois restriction. -/
def originalFullIdeleBaseChangeRepHom :
    Rep.res (galoisBaseChangeRestriction K E L M) (originalFullIdeleRep K L) ⟶
      originalFullIdeleRep E M :=
  Rep.ofHom ⟨(originalIdeleBaseChangeMap L M).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul
      (originalIdeleBaseChangeMap_restrictNormal K L M (σ.restrictScalars K) x.toMul).symm⟩

/-- Actual idele-class inclusion with the same genuine field restriction. -/
def originalFullClassFieldBaseChangeRepHom :
    Rep.res (galoisBaseChangeRestriction K E L M) (originalIdeleClassRep K L) ⟶
      originalIdeleClassRep E M :=
  Rep.ofHom ⟨(originalFullClassBaseChangeRepHom K L M).hom.toLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    exact Rep.hom_comm_apply (originalFullClassBaseChangeRepHom K L M)
      (σ.restrictScalars K) x⟩

/-- The original full-idele H2 map induced by actual field base change. -/
def originalFullIdeleBaseChangeH2 :
    groupCohomology (originalFullIdeleRep K L) 2 ⟶
      groupCohomology (originalFullIdeleRep E M) 2 :=
  groupCohomology.map (galoisBaseChangeRestriction K E L M)
    (originalFullIdeleBaseChangeRepHom K E L M) 2

/-- Base change of an actual principal class is the principal class of its actual unit base change. -/
theorem originalFullIdeleBaseChangeH2_principal
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    originalFullIdeleBaseChangeH2 K E L M
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) =
      (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullPrincipalRepHom E M)
        (groupCohomology.map (galoisBaseChangeRestriction K E L M)
          (galoisUnitBaseChangeInclusion K E L M) 2 x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    exact congrArg Additive.ofMul (originalIdeleBaseChangeMap_principal L M _)

/-- Projecting the actually base-changed idele class agrees with base-changing its actual class projection. -/
theorem originalFullIdeleBaseChangeH2_class
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      (originalFullIdeleBaseChangeH2 K E L M x) =
      groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (originalFullClassFieldBaseChangeRepHom K E L M) 2
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_mk L M _).symm

end
end Dubon2026
