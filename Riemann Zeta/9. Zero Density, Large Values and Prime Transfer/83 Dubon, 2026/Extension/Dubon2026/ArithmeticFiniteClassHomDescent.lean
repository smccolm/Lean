import Dubon2026.FiniteCoefficientColimitHomDescent
import Dubon2026.ArithmeticFiniteStageActionContinuity
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Actual finite-stage descent of arithmetic full-class morphisms

An invariant full-class Hom coefficient is an actual equivariant morphism.
The finite coefficient and compact arithmetic action put it in one finite
class quotient above its original field. This supplies the degree-zero
class-Hom term of DUB-17's source class/Ext comparison. Relation-lattice
descent, local cup and reverse-localization comparisons remain separate.
-/
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

/-- Every actual finite-coefficient morphism into the original full-class
colimit lifts equivariantly to one original class stage containing its
source field, with the literal colimit inclusion unchanged. -/
theorem arithmeticFiniteClassHom_exists_stage
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B ⟶
        arithmeticClassesModOutsideColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      P ≤ N ∧ ∃ ψ : Rep.res (AlgEquiv.restrictNormalHom P :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B ⟶
          arithmeticGlobalClassesModOutsideStageRep K Ω a ha N,
        ψ ≫ coefficientRepresentationColimitOf _
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N = φ := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  let A := Rep.res (AlgEquiv.restrictNormalHom P :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha) := ⊥
  letI : DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha) := ⟨rfl⟩
  letI : ∀ F, TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) :=
    fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) :=
    fun _ => ⟨rfl⟩
  letI : DirectedSystem (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticClassesModOutsideDirectedSystem K Ω a ha
  have hA (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
      Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticGlobalClassesModOutsideStageRep K Ω a ha F =>
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).ρ z.1 z.2) :=
    restrictedCoefficientAction_continuous (arithmeticClassesModOutsideStageRep K Ω a ha F) _
      (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) continuous_of_discreteTopology
  exact finiteCoefficientColimitHom_exists_stage_ge
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) A hA
    (arithmeticFiniteStageRepresentationAction_continuous K Ω a P B) P φ

end
end Dubon2026
