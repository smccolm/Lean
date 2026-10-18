import Dubon2026.OriginalSinglePrimeTraceCoefficients
import Dubon2026.OriginalSPlaceFullClassImage
import Dubon2026.OriginalRelationModuleSequence

/-! Assemble the actual local relation morphism into the original S-place
coefficient. Native restriction/coinduction adjunction and the proved
single-prime trace recover the chosen local values and vanish outside its
orbit. This supplies DUB-17's finite local-family construction without a
new general source-Hom H1 isomorphism. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (w : HeightOneSpectrum (𝓞 L))
  [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)]
  (B : Rep.{0} ℤ Gal(L/K))

/-- The actual local relation morphism under the native coinduction adjunction. -/
def originalLocalRelationCoinduced
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) :
    originalRelationModule B ⟶
      Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w) :=
  Rep.resCoindToHom (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B)
    (originalAdicUnitRep K L w) φ

/-- The original local relation morphism traced into the actual full ideles. -/
def originalSinglePrimeFullRelation
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) :
    originalRelationModule B ⟶ originalFullIdeleRep K L :=
  originalLocalRelationCoinduced K L w B φ ≫ originalSinglePrimeCoinducedTrace K L w

/-- The same constructed relation morphism in the original finite S-place coefficient. -/
def originalSinglePrimeSPlaceRelation
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) :
    originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS :=
  originalSinglePrimeFullRelation K L w B φ ≫ originalFullUnrestrictedRepHom K L S hS

omit S hS in
/-- The original single-prime relation construction recovers every original
local relation value at the chosen completion. -/
theorem originalSinglePrimeFullRelation_evaluation
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) (x : originalRelationModule B) :
    (originalFullIdeleAdicRepHom K L w).hom ((originalSinglePrimeFullRelation K L w B φ).hom x) =
      φ.hom x := by
  change (originalFullIdeleAdicRepHom K L w).hom
    ((originalSinglePrimeCoinducedTrace K L w).hom ((originalLocalRelationCoinduced K L w B φ).hom x)) = _
  rw [originalSinglePrimeCoinducedTrace_evaluation]
  change φ.hom ((originalRelationModule B).ρ 1 x) = φ.hom x
  rw [map_one, Module.End.one_apply]

/-- The original S-place relation map has exactly the specified local value. -/
theorem originalSinglePrimeSPlaceRelation_evaluation (hw : w ∈ S)
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) (x : originalRelationModule B) :
    (originalSinglePrimeSPlaceRelation K L S hS w B φ).hom x (Sum.inr ⟨w, hw⟩) = φ.hom x :=
  originalSinglePrimeFullRelation_evaluation K L w B φ x

/-- At an S-place outside the chosen prime's original orbit the constructed
relation value is zero; no extraneous local class is introduced there. -/
theorem originalSinglePrimeSPlaceRelation_outside_orbit
    (v : S) (hv : ∀ σ : Gal(L/K), numberFieldGaloisPlaceEquiv K L σ w ≠ v.val)
    (φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w) (x : originalRelationModule B) :
    (originalSinglePrimeSPlaceRelation K L S hS w B φ).hom x (Sum.inr v) = 0 :=
  originalSinglePrimeCoinducedTrace_outside_orbit K L w v.val hv
    ((originalLocalRelationCoinduced K L w B φ).hom x)

end
end Dubon2026
