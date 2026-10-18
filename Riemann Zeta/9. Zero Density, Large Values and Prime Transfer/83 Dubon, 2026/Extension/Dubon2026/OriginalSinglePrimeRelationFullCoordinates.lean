import Dubon2026.OriginalSinglePrimeSPlaceRelation
import Dubon2026.OriginalSPlaceFullIdeleCoordinates

/-! The finite S-place relation construction retains the native single-prime
trace at every original finite coordinate after full-idele inclusion.
This supplies the precise source representative needed for DUB-17's
canonical total comparison, without a full-idele H2 surjectivity premise. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (w : HeightOneSpectrum (𝓞 L)) (hw : w ∈ S)
  [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)]
  (B : Rep.{0} ℤ Gal(L/K))

include hw in
/-- The actual S-place representative and native full-idele trace have the
same value at every finite completion, with outside support derived. -/
theorem originalSinglePrimeSPlaceRelation_full_coordinate
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) (x : originalRelationModule B)
    (v : HeightOneSpectrum (𝓞 L)) :
    (originalFullIdeleAdicRepHom K L v).hom
      ((originalSPlaceFullIdeleInclusion K L S hS).hom
        ((originalSinglePrimeSPlaceRelation K L S hS w B φ).hom x)) =
      (originalFullIdeleAdicRepHom K L v).hom ((originalSinglePrimeFullRelation K L w B φ).hom x) := by
  by_cases hv : v ∈ S
  · exact originalSPlaceFullIdeleInclusion_finite K L S hS
      ((originalSinglePrimeSPlaceRelation K L S hS w B φ).hom x) ⟨v, hv⟩
  · rw [originalSPlaceFullIdeleInclusion_outside K L S hS _ v hv]
    symm
    apply originalSinglePrimeCoinducedTrace_outside_orbit K L w v
    intro σ hσ
    exact hv (hσ ▸ (hS σ w).mp hw)

end
end Dubon2026
