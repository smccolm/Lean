import Dubon2026.OriginalSPlaceFullIdeleCoordinates
import Dubon2026.OriginalAdicUnitRelationTransport
import Dubon2026.OriginalFullIdeleCompletionCocycle
import Dubon2026.OriginalRestrictedRelationObstruction

/-! The finite S-place relation obstruction at its literal completion.
Native completion localization and connecting naturality identify the finite
class used by the canonical invariant with the specified local relation. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (v : HeightOneSpectrum (𝓞 K)) (w : S) [w.val.asIdeal.LiesOver v.asIdeal]
  (B : Rep.{0} ℤ Gal(L/K))

/-- The actual finite S-place relation localizes to the specified completion
relation whenever their literal unit values agree. The cohomological
comparison is derived from that coefficient identity. -/
theorem originalSPlaceRelation_completion_obstruction
    (Φ : originalRelationModule B ⟶ supportedUnrestrictedUnitRep K L S hS)
    (ψ : Rep.res (originalAdicCompletionGaloisInclusion K L v w.val)
      (originalRelationModule B) ⟶ Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.val.adicCompletion L))
    (heval : ∀ x : originalRelationModule B, Φ.hom x (Sum.inr w) = ψ.hom x)
    (y : groupCohomology B 1) :
    originalFullIdeleCompletionH2 K L v w.val
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
        (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS) Φ y)) =
    (groupCohomology.functor ℤ Gal(w.val.adicCompletion L/v.adicCompletion K) 2).map ψ
      (groupCohomology.δ (originalRelationGroupChange_shortExact
        (originalAdicCompletionGaloisInclusion K L v w.val) B) 1 2 rfl
        (groupCohomology.map (originalAdicCompletionGaloisInclusion K L v w.val)
          (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L v w.val) B)) 1 y)) := by
  let π := originalAdicCompletionGaloisInclusion K L v w.val
  let inc := originalSPlaceFullIdeleInclusion K L S hS
  let j := originalFullIdeleCompletionRepHom K L v w.val
  let jS : Rep.res π (supportedUnrestrictedUnitRep K L S hS) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.val.adicCompletion L) :=
    (Rep.resFunctor π).map inc ≫ j
  have he : (Rep.resFunctor π).map Φ ≫ jS = ψ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (originalSPlaceFullIdeleInclusion_finite K L S hS (Φ.hom x) w).trans (heval x)
  have h := originalRestrictedRelation_obstruction_inflation π B
    (supportedUnrestrictedUnitRep K L S hS)
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.val.adicCompletion L)) Φ jS
  erw [he] at h
  have hv := congrArg (fun m => m.hom y) h
  rw [originalFullIdeleCompletionH2_eq_map]
  have hm := groupCohomology.map_comp
    (A := supportedUnrestrictedUnitRep K L S hS) (B := originalFullIdeleRep K L)
    (C := Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.val.adicCompletion L))
    (MonoidHom.id Gal(L/K)) π inc j 2
  have hc := congrArg (fun m => m.hom
    (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS) Φ y)) hm
  exact hc.symm.trans hv

end
end Dubon2026
