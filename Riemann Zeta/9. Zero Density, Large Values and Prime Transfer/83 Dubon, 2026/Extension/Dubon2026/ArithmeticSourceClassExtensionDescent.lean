import Dubon2026.ArithmeticFreeSourceClassHomDescent
import Dubon2026.FiniteLatticeColimitEqualityDescent
import Dubon2026.OriginalFiniteRelationModule

/-! Descend the actual source-class extension and its relation equation
to the same finite field. Native finite-lattice descent handles the free
cover; finite-basis zero detection preserves the original relation map.
This removes the finite-stage compatibility premise before DUB-17's
projective lift to S-place ideles and global S-unit H1 construction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

private theorem sourceStage_colimit_comp
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F hEF ≫
      coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) F =
        coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) E := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact Module.DirectLimit.of_f (hij := hEF)

variable (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- A source-class extension of the actual finite relation descends to
one larger arithmetic field, retaining both its colimit value and its
exact relation equation at that field. -/
theorem arithmeticSourceClassExtension_exists_stage_with_relation :
    let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K) :=
      AlgEquiv.restrictNormalHom P
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    ∀ (φ : X.X₁ ⟶ arithmeticGlobalSPlaceClassStageRep K Ω a ha P)
      (f : X.X₂ ⟶ arithmeticSPlaceClassColimitRep K Ω a ha),
      X.f ≫ f = φ ≫ coefficientRepresentationColimitOf _
        (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P →
      ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
        ∃ fN : X.X₂ ⟶ arithmeticGlobalSPlaceClassStageRep K Ω a ha N,
          fN ≫ coefficientRepresentationColimitOf _
            (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) N = f ∧
          X.f ≫ fN = φ ≫ arithmeticGlobalSPlaceClassStageTransition K Ω a ha P N hPN := by
  intro π X φ f hf
  obtain ⟨N, hPN, ψ, hψ⟩ := arithmeticFreeSourceClassHom_exists_stage K Ω a ha P B f
  let φN := φ ≫ arithmeticGlobalSPlaceClassStageTransition K Ω a ha P N hPN
  let ofN := coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) N
  have he : (X.f ≫ ψ) ≫ ofN = φN ≫ ofN := by
    have hleft : (X.f ≫ ψ) ≫ ofN = X.f ≫ f := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro r
      exact congrArg (fun m => m.hom (X.f.hom r)) hψ
    have hright : φN ≫ ofN = φ ≫ coefficientRepresentationColimitOf _
        (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro r
      exact Module.DirectLimit.of_f (hij := hPN)
    exact hleft.trans (hf.trans hright.symm)
  letI : Module.Finite ℤ X.X₁ := originalRelationModule_finite B
  letI : Module.Free ℤ X.X₁ := originalRelationModule_free B
  letI : DirectedSystem (fun F => arithmeticGlobalSPlaceClassStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticSPlaceClassDirectedSystem K Ω a ha
  have he' : ofN.hom.toLinearMap.comp (X.f ≫ ψ).hom.toLinearMap =
      ofN.hom.toLinearMap.comp φN.hom.toLinearMap :=
    congrArg (fun m : X.X₁ ⟶ arithmeticSPlaceClassColimitRep K Ω a ha => m.hom.toLinearMap) he
  obtain ⟨M, hNM, hM⟩ := finiteLatticeColimitEquality_exists_stage
    (fun F => arithmeticGlobalSPlaceClassStageRep K Ω a ha F)
    (fun E F h => (arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F h).hom.toLinearMap)
    X.X₁ N (X.f ≫ ψ).hom.toLinearMap φN.hom.toLinearMap he'
  let fM := ψ ≫ arithmeticGlobalSPlaceClassStageTransition K Ω a ha N M hNM
  refine ⟨M, hPN.trans hNM, fM, ?_, ?_⟩
  · exact (Category.assoc ψ
      (arithmeticGlobalSPlaceClassStageTransition K Ω a ha N M hNM)
      (coefficientRepresentationColimitOf _
        (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) M)).trans
      ((congrArg (fun m => ψ ≫ m) (sourceStage_colimit_comp K Ω a ha N M hNM)).trans hψ)
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    exact (LinearMap.congr_fun hM r).trans
      (arithmeticSPlaceClassTransitionMap_comp K Ω a ha P N M hPN hNM (φ.hom r))

end
end Dubon2026
