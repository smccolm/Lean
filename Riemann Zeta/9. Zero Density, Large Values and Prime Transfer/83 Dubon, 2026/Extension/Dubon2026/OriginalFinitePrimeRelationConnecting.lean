import Dubon2026.OriginalFinitePrimeSPlaceRelation
import Dubon2026.OriginalSPlaceFullIdeleCoordinates
import Dubon2026.OriginalRestrictedRelationObstruction

/-! The assembled finite S-place relation has the specified original local
connecting obstruction at every selected prime. Native connecting
naturality and the proved exact coordinate recovery give the local square
used by DUB-17's invariant sum, without a localization-equality premise. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
attribute [local instance] finitePrimeRelationCosets
variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 K))) (w : T → S)
  (B : Rep.{0} ℤ Gal(L/K))

/-- The actual S-place-to-completion coefficient map through the original full ideles. -/
def originalSPlaceAdicRelationEvaluation (v : S) :
    Rep.res (OriginalFiniteDecompositionGroup K L v.val).subtype (supportedUnrestrictedUnitRep K L S hS) ⟶
      originalAdicUnitRep K L v.val :=
  (Rep.resFunctor (OriginalFiniteDecompositionGroup K L v.val).subtype).map
    (originalSPlaceFullIdeleInclusion K L S hS) ≫ originalFullIdeleAdicRepHom K L v.val

omit [NumberField K] in
/-- Localization of the assembled original relation obstruction is exactly
the original local relation applied to the restricted connecting class. -/
theorem originalFinitePrimeSPlaceRelation_connecting
    (hw : ∀ v : T, originalFinitePrimeBelow K L (w v).val = v.val)
    (φ : ∀ v : T,
      Rep.res (OriginalFiniteDecompositionGroup K L (w v).val).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L (w v).val) (v : T) :
    originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
        (originalFinitePrimeSPlaceRelation K L S hS T w B φ) ≫
      groupCohomology.map (OriginalFiniteDecompositionGroup K L (w v).val).subtype
        (originalSPlaceAdicRelationEvaluation K L S hS (w v)) 2 =
    groupCohomology.map (OriginalFiniteDecompositionGroup K L (w v).val).subtype
        (𝟙 (Rep.res (OriginalFiniteDecompositionGroup K L (w v).val).subtype B)) 1 ≫
      groupCohomology.δ
        (originalRelationGroupChange_shortExact (OriginalFiniteDecompositionGroup K L (w v).val).subtype B)
        1 2 rfl ≫
      (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L (w v).val) 2).map (φ v) := by
  let π := (OriginalFiniteDecompositionGroup K L (w v).val).subtype
  let Φ := originalFinitePrimeSPlaceRelation K L S hS T w B φ
  let j := originalSPlaceAdicRelationEvaluation K L S hS (w v)
  have he : (Rep.resFunctor π).map Φ ≫ j = φ v := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (originalSPlaceFullIdeleInclusion_finite K L S hS (Φ.hom x) (w v)).trans
      (originalFinitePrimeSPlaceRelation_evaluation K L S hS T w B hw φ v x)
  have h := originalRestrictedRelation_obstruction_inflation π B
    (supportedUnrestrictedUnitRep K L S hS) (originalAdicUnitRep K L (w v).val) Φ j
  erw [he] at h
  exact h

end
end Dubon2026
