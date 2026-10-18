import Dubon2026.FiniteLatticeColimitHomDescent
import Dubon2026.ArithmeticFiniteStageActionContinuity
import Dubon2026.ArithmeticSPlaceCoefficientColimits

/-! Descend the source-class free-cover extension to one actual finite
arithmetic stage. The original finite free lattice and compact Galois
action meet the already proved finite-lattice descent theorem. This is
the finite-stage input for DUB-17's projective lift to S-place ideles. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- The actual restricted free cover's source-class morphism descends
equivariantly above its coefficient field, with its literal colimit value. -/
theorem arithmeticFreeSourceClassHom_exists_stage
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K))
        (Rep.free ℤ Gal(P/K) B) ⟶ arithmeticSPlaceClassColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      P ≤ N ∧ ∃ ψ : Rep.res (AlgEquiv.restrictNormalHom P :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K))
          (Rep.free ℤ Gal(P/K) B) ⟶ arithmeticGlobalSPlaceClassStageRep K Ω a ha N,
        ψ ≫ coefficientRepresentationColimitOf _
          (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) N = φ := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  let A := Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) (Rep.free ℤ Gal(P/K) B)
  letI : Module.Finite ℤ A := by
    change Module.Finite ℤ (B →₀ Gal(P/K) →₀ ℤ)
    infer_instance
  letI : Module.Free ℤ A := by
    change Module.Free ℤ (B →₀ Gal(P/K) →₀ ℤ)
    infer_instance
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace (arithmeticSPlaceClassColimitRep K Ω a ha) := ⊥
  letI : DiscreteTopology (arithmeticSPlaceClassColimitRep K Ω a ha) := ⟨rfl⟩
  letI : ∀ F, TopologicalSpace (arithmeticGlobalSPlaceClassStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalSPlaceClassStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  letI : DirectedSystem (fun F => arithmeticGlobalSPlaceClassStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticSPlaceClassDirectedSystem K Ω a ha
  have hA (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
      Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticGlobalSPlaceClassStageRep K Ω a ha F =>
          (arithmeticGlobalSPlaceClassStageRep K Ω a ha F).ρ z.1 z.2) :=
    restrictedCoefficientAction_continuous (ArithmeticSPlaceClassFiniteStageRep K Ω a ha F) _
      (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) continuous_of_discreteTopology
  exact finiteLatticeColimitHom_exists_stage_ge
    (arithmeticGlobalSPlaceClassStageRep K Ω a ha)
    (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) A hA
    (arithmeticFiniteStageRepresentationAction_continuous K Ω a P (Rep.free ℤ Gal(P/K) B)) P φ

end
end Dubon2026
