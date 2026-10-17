import Dubon2026.ArithmeticClassStageContinuousCocycle
import Dubon2026.OriginalTwoCocycleSurjectiveBoundary
import Dubon2026.ArithmeticOpenSubgroupClassH2ZeroDetection

/-! # Continuous equality has an actual finite arithmetic witness

Apply this to the difference between the source-induced finite class and
the enlarged scalar obstruction after their coefficient stages are placed
in a common field. The existing continuous coboundary descent constructs
the larger stage; no injectivity of global continuous-to-algebraic H2 is used.
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

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticClassStageFiniteBoundaryLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- The actual continuous zero supplies a concrete finite cochain boundary
above the original arithmetic coefficient stage, preserving all values. -/
theorem arithmeticClassStageContinuousH2_zero_exists_finite_boundary
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E))
    (hz : (Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha E c) :
      ContinuousRepresentationH2 (arithmeticClassesModOutsideColimitRep K Ω a ha)
        (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)) = 0) :
    let H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) := ⊤
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEF : E ≤ F,
        let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
        ∃ d : π.range → arithmeticClassesModOutsideStageRep K Ω a ha F,
          ∀ g h : H, (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom
            (c (AlgEquiv.restrictNormalHom E g.val, AlgEquiv.restrictNormalHom E h.val)) =
              (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).ρ g.val (d (π.rangeRestrict h)) -
                d (π.rangeRestrict (g * h)) + d (π.rangeRestrict g) := by
  intro H
  let D := arithmeticClassesModOutsideColimitRep K Ω a ha
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  let bH : C(H, D) := ⟨fun g => b g.val, b.continuous.comp continuous_subtype_val⟩
  let u : H × H → arithmeticClassesModOutsideStageRep K Ω a ha E := fun z =>
    c (AlgEquiv.restrictNormalHom E z.1.val, AlgEquiv.restrictNormalHom E z.2.val)
  have hu (g h : H) : (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (u (g, h)) =
        D.ρ g.val (bH h) - bH (g * h) + bH g := by
    have he := congrArg (fun z : continuousRepresentationCocyclesTwo D => z.val (g.val, h.val)) hb
    exact he.symm
  exact arithmeticOpenSubgroupClassCoboundary_exists_finite_witness K Ω a ha H E u bH hu

end
end Dubon2026
