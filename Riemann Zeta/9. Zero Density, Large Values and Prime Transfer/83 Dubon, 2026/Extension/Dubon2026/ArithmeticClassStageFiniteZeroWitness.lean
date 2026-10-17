import Dubon2026.ArithmeticClassStageFiniteBoundary
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
local instance arithmeticClassStageFiniteZeroWitnessLocalInstance1 : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Zero of the literal finite cocycle in continuous arithmetic class H2
constructs a larger finite field where its actual finite inflation is zero. -/
theorem arithmeticClassStageContinuousH2_zero_exists_finite_witness
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : groupCohomology.cocycles₂ (arithmeticClassesModOutsideStageRep K Ω a ha E))
    (hz : (Submodule.Quotient.mk (arithmeticClassStageContinuousTwoCocycle K Ω a ha E c) :
      ContinuousRepresentationH2 (arithmeticClassesModOutsideColimitRep K Ω a ha)
        (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)) = 0) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEF : E ≤ F,
        letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
        letI : Module E F := Algebra.toModule
        letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
        letI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
        letI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
          IsScalarTower.of_algebraMap_eq' rfl
        groupCohomology.map (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K))
          (arithmeticClassesModOutsideFiniteTransition K Ω a ha E F hEF) 2
          (groupCohomology.H2π _ c) = 0 := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  let G := Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
  let H : OpenSubgroup G := ⊤
  obtain ⟨F, hEF, d, hd⟩ := arithmeticClassStageContinuousH2_zero_exists_finite_boundary
    K Ω a ha E c hz
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  letI : SMul E F := ((IntermediateField.inclusion hEF).toAlgebra).toSMul
  letI : IsScalarTower K E F := IsScalarTower.of_algHom (IntermediateField.inclusion hEF)
  letI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
  have hπ : Function.Surjective π := by
    intro σ
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
      (originalUnramifiedGaloisUnion (Ω := Ω) a) σ
    exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩
  refine ⟨F, hEF, ?_⟩
  rw [groupCohomology.H2π_comp_map_apply]
  apply originalTwoCocycle_H2_zero_of_surjective_range_boundary π hπ _ _ d
  intro g h
  change (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom
    (c ((AlgEquiv.restrictNormalHom E) ((AlgEquiv.restrictNormalHom F) g.val),
      (AlgEquiv.restrictNormalHom E) ((AlgEquiv.restrictNormalHom F) h.val))) = _
  rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F g.val,
    ← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F h.val]
  exact hd g h

end
end Dubon2026
