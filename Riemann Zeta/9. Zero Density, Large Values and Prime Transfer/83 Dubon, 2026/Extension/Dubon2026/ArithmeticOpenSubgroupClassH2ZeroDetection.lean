import Dubon2026.ArithmeticOpenSubgroupClassCochainDescent
import Dubon2026.ArithmeticClassQuotientTransitionInjectivity

/-! # Original continuous class coboundaries have finite arithmetic witnesses

The actual continuous one-cochain descends above the supplied coefficient
stage. Injectivity of the original stage inclusion reflects its precise
differential identity. This detects zero classes by a finite witness,
needed for a representative-independent H2 invariant in DUB-17's global
duality route. It does not assume an invariant map or global duality.
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

/-- An actual continuous coboundary relation on an original finite-stage two-cochain is witnessed over a larger original finite Galois image. -/
theorem arithmeticOpenSubgroupClassCoboundary_exists_finite_witness
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (u : H × H → arithmeticClassesModOutsideStageRep K Ω a ha E)
    (b : C(H, arithmeticClassesModOutsideColimitRep K Ω a ha))
    (hb : ∀ g h : H, (coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (u (g, h)) =
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val (b h) - b (g * h) + b g) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a), ∃ hEF : E ≤ F,
      let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : π.range → arithmeticClassesModOutsideStageRep K Ω a ha F,
        ∀ g h : H, (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom (u (g, h)) =
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).ρ g.val (d (π.rangeRestrict h)) -
            d (π.rangeRestrict (g * h)) + d (π.rangeRestrict g) := by
  have hDescent := arithmeticOpenSubgroupClassCochain_exists_finite_descent K Ω a ha H E b
  obtain ⟨F, hEF, d, hd⟩ := hDescent
  let iE := coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E
  let iF := coefficientRepresentationColimitOf
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
    (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F
  let φ := arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF
  have hmap (x : arithmeticClassesModOutsideStageRep K Ω a ha E) :
      iF.hom (φ.hom x) = iE.hom x :=
    Module.DirectLimit.of_f (R := ℤ)
      (G := fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (f := fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
      (hij := hEF) (x := x)
  refine ⟨F, hEF, d, ?_⟩
  intro g h
  apply arithmeticClassesModOutsideColimitOf_injective K Ω a ha F
  change iF.hom (φ.hom (u (g, h))) = _
  rw [hmap, map_add, map_sub, Rep.hom_comm_apply, hd, hd, hd]
  exact hb g h

/-- Scalar multiplication on the original discrete class coefficient is continuous. -/
local instance classH2ZeroContinuousSMul : @ContinuousSMul ℤ (arithmeticClassesModOutsideColimitRep K Ω a ha)
    (arithmeticClassesModOutsideColimitRep K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Each actual open arithmetic subgroup inherits its topological group structure. -/
local instance classH2ZeroTopologicalGroup
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K)) :
    IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- Zero in the actual continuous class H2 quotient supplies an original finite arithmetic coboundary witness for every original finite representative. -/
theorem arithmeticOpenSubgroupClassH2_zero_exists_finite_witness
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (u : H × H → arithmeticClassesModOutsideStageRep K Ω a ha E)
    (c : continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (arithmeticClassesModOutsideColimitRep K Ω a ha) H.toSubgroup.subtype))
    (hu : ∀ z, (coefficientRepresentationColimitOf
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
        (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom (u z) = c.val z)
    (hz : (Submodule.Quotient.mk c : ContinuousRepresentationH2
      (restrictedCoefficientRep (arithmeticClassesModOutsideColimitRep K Ω a ha) H.toSubgroup.subtype)
      (restrictedCoefficientAction_continuous _ H.toSubgroup.subtype continuous_subtype_val
        (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha))) = 0) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a), ∃ hEF : E ≤ F,
      let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : π.range → arithmeticClassesModOutsideStageRep K Ω a ha F,
        ∀ g h : H, (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom (u (g, h)) =
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).ρ g.val (d (π.rangeRestrict h)) -
            d (π.rangeRestrict (g * h)) + d (π.rangeRestrict g) := by
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  apply arithmeticOpenSubgroupClassCoboundary_exists_finite_witness K Ω a ha H E u b
  intro g h
  have he := congrArg (fun z : continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (arithmeticClassesModOutsideColimitRep K Ω a ha) H.toSubgroup.subtype) =>
        z.val (g, h)) hb
  exact (hu (g, h)).trans he.symm

end
end Dubon2026
