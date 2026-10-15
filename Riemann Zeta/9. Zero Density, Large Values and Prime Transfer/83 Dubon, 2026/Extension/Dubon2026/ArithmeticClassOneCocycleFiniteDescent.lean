import Dubon2026.ContinuousCoefficientColimitCocycleLift
import Dubon2026.ContinuousGaloisFunctionFinitePeriods
import Dubon2026.RestrictedOneCocycleDescent
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Actual finite-stage descent of arithmetic class one-cocycles

The compact coefficient lift and original Galois periods put each actual
continuous class-colimit cocycle in a genuine finite arithmetic field,
retaining its values under the original quotient transition. This is the
precise input to finite-stage class H1 vanishing for DUB-17 class formation.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)]

/-- The original coefficient structure used in this comparison. -/
local instance classCocycleDescentSMul : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Every actual continuous arithmetic class cocycle descends to the original quotient at one finite Galois stage, with unchanged representative values. -/
theorem arithmeticClassOneCocycle_exists_finite_descent
    (c : continuousRepresentationCocyclesOne (arithmeticClassesModOutsideColimitRep K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ d : groupCohomology.cocycles₁ (arithmeticClassesModOutsideStageRep K Ω a ha F),
        ∀ g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
          (coefficientRepresentationColimitOf _ (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
            (d (AlgEquiv.restrictNormalHom F g)) = c.val g := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : ∀ F, TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  letI : DirectedSystem (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticClassesModOutsideDirectedSystem K Ω a ha
  have hA (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
      Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticGlobalClassesModOutsideStageRep K Ω a ha F =>
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).ρ z.1 z.2) :=
    restrictedCoefficientAction_continuous (arithmeticClassesModOutsideStageRep K Ω a ha F) _
      (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) continuous_of_discreteTopology
  obtain ⟨E, b, hb⟩ := continuousCoefficientColimitOneCocycle_exists_lift
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) hA c
  obtain ⟨F, hEF, hp⟩ := continuousGaloisFunction_exists_finite_periods E
    (show C(Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
      arithmeticGlobalClassesModOutsideStageRep K Ω a ha E) from ⟨fun g => b.val g, b.property⟩)
  let φ := arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF
  let bF : groupCohomology.cocycles₁ (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) :=
    ⟨fun g => φ.hom (b.val g), by
      apply (groupCohomology.mem_cocycles₁_iff _).mpr
      intro g h
      have hc : b.val (g * h) =
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E).ρ g (b.val h) + b.val g :=
        (groupCohomology.mem_cocycles₁_iff _).mp b.val.property g h
      exact (congrArg φ.hom hc).trans (by rw [map_add, Rep.hom_comm_apply])⟩
  let j : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K) :=
    AlgEquiv.restrictNormalHom F
  have hj : Function.Surjective j := AlgEquiv.restrictNormalHom_surjective _
  have hperiod (g h) (he : j g = j h) : bF g = bF h := by
    have hk : j (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have hv := hp g (g⁻¹ * h) hk
    have hv' : b.val g = b.val h := by simpa only [mul_inv_cancel_left] using hv.symm
    exact congrArg φ.hom hv'
  obtain ⟨d, hd⟩ := restrictedOneCocycle_exists_descent
    (arithmeticClassesModOutsideStageRep K Ω a ha F) j hj bF hperiod
  refine ⟨F, d, ?_⟩
  intro g
  rw [hd g]
  change Module.DirectLimit.of ℤ _
    (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    F ((arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom.toLinearMap (b.val g)) = _
  exact (Module.DirectLimit.of_f (R := ℤ)
    (G := fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (f := fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (hij := hEF) (x := b.val g)).trans (hb g)

end
end Dubon2026
