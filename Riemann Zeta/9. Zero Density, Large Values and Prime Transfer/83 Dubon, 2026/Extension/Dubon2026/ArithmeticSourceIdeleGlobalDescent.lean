import Dubon2026.ArithmeticSourceIdeleTwoCocycleDescent
import Dubon2026.OriginalTwoCocycleSurjectiveRange

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticSPlaceColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticSPlaceColimitRep K Ω a ha)]

/-- The original continuous action, named to preserve distinct production declarations. -/
local instance arithmeticSourceIdeleGlobalDescentLocalInstance1 : @ContinuousSMul ℤ (arithmeticSPlaceColimitRep K Ω a ha)
    (arithmeticSPlaceColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (arithmeticSPlaceColimitRep K Ω a ha)
    (arithmeticSPlaceColimitRep K Ω a ha).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Every actual continuous source-idele two-cocycle has a finite Galois
representative with unchanged original coefficient values. -/
theorem arithmeticSourceIdeleContinuousTwoCocycle_exists_finite_descent
    (c : continuousRepresentationCocyclesTwo (arithmeticSPlaceColimitRep K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep K Ω a ha F),
        ∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
          (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep K Ω a ha)
            (arithmeticGlobalSPlaceStageTransition K Ω a ha) F).hom
              (d (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) = c.val (g, h) := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  let G := Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)
  let H : OpenSubgroup G := ⊤
  have hc : Continuous (fun z : H × H => c.val (z.1.val, z.2.val)) :=
    c.property.comp (continuous_subtype_val.prodMap continuous_subtype_val)
  have hcc (g h k : H) : c.val ((g * h).val, k.val) + c.val (g.val, h.val) =
      (arithmeticSPlaceColimitRep K Ω a ha).ρ g.val (c.val (h.val, k.val)) +
        c.val (g.val, (h * k).val) :=
    (groupCohomology.mem_cocycles₂_iff _).mp c.val.property g.val h.val k.val
  obtain ⟨F, d, hd⟩ := arithmeticSourceIdeleTwoCocycle_exists_finite_descent
    K Ω a ha H (fun z => c.val (z.1.val, z.2.val)) hc hcc
  let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
  have hπ : Function.Surjective π := by
    intro σ
    obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
      (originalUnramifiedGaloisUnion (Ω := Ω) a) σ
    exact ⟨⟨g, Subgroup.mem_top g⟩, hg⟩
  obtain ⟨dF, hdF⟩ := originalTwoCocycle_surjective_range π hπ
    (ArithmeticSPlaceFiniteStageRep K Ω a ha F) d
  refine ⟨F, dF, ?_⟩
  intro g h
  have he := hdF ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
  exact (congrArg (coefficientRepresentationColimitOf (arithmeticGlobalSPlaceStageRep K Ω a ha)
    (arithmeticGlobalSPlaceStageTransition K Ω a ha) F).hom he).trans
      (hd ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩)

end
end Dubon2026
