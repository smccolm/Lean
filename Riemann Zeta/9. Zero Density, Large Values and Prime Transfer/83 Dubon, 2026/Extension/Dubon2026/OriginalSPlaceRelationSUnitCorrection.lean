import Dubon2026.OriginalSPlaceIdeleSequence
import Dubon2026.OriginalRelationModuleSequence

/-! Lift the actual free-cover class extension through the S-place
quotient. Its difference from the prescribed idele relation lands in
the original diagonal S-units. This is the finite-stage input to the
proved S-unit dual connecting map on DUB-17's reverse-localization chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (B : Rep.{0} ℤ Gal(L/K))

/-- A class extension of the actual idele relation has a projective idele
lift whose relation defect is an original diagonal S-unit morphism. -/
theorem originalSPlaceRelation_exists_SUnit_correction
    (ψ : originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS)
    (f : Rep.free ℤ Gal(L/K) B ⟶ originalSPlaceIdeleClassRep K L S hS)
    (hf : originalRelationInclusion B ≫ f = ψ ≫ originalSPlaceIdeleClassRepHom K L S hS) :
    ∃ l : Rep.free ℤ Gal(L/K) B ⟶ supportedUnrestrictedUnitRep K L S hS,
      ∃ η : originalRelationModule B ⟶ sUnitOriginalRep K L S hS,
        l ≫ originalSPlaceIdeleClassRepHom K L S hS = f ∧
        η ≫ originalSPlacePrincipalRepHom K L S hS = ψ - originalRelationInclusion B ≫ l := by
  have hX := originalSPlaceIdeleShortComplex_shortExact K L S hS
  letI : Epi (originalSPlaceIdeleClassRepHom K L S hS) := hX.epi_g
  letI : Mono (originalSPlacePrincipalRepHom K L S hS) := hX.mono_f
  let l : Rep.free ℤ Gal(L/K) B ⟶ supportedUnrestrictedUnitRep K L S hS :=
    Projective.factorThru f (originalSPlaceIdeleClassRepHom K L S hS)
  have hl : l ≫ originalSPlaceIdeleClassRepHom K L S hS = f :=
    Projective.factorThru_comp f (originalSPlaceIdeleClassRepHom K L S hS)
  let δ : originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS :=
    ψ - originalRelationInclusion B ≫ l
  have hδ : δ ≫ originalSPlaceIdeleClassRepHom K L S hS = 0 := by
    change (ψ - originalRelationInclusion B ≫ l) ≫ originalSPlaceIdeleClassRepHom K L S hS = 0
    rw [Preadditive.sub_comp, Category.assoc, hl, hf, sub_self]
  letI : Mono (originalSPlaceIdeleShortComplex K L S hS).f := hX.mono_f
  exact ⟨l, hX.exact.lift δ hδ, hl, hX.exact.lift_f δ hδ⟩

end
end Dubon2026
