import Dubon2026.ArithmeticSUnitH2FiniteTransitions
import Dubon2026.ArithmeticSUnitCochainFiniteDescent

/-! # Continuous S-unit coboundaries vanish at genuine finite stages

The original continuous S-unit witness descends to a finite stage. Injectivity
of the literal coefficient inclusion and surjectivity of Galois restriction
reflect its differential there. This proves the zero-detection input for the
actual S-unit H2 colimit, needed by the DUB-17 global-duality route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

private theorem coboundary_reflection
    {R G H : Type} [CommRing R] [Group G] [Group H]
    (A : Rep R G) (B : Rep R H) (j : H →* G) (hj : Function.Surjective j)
    (φ : restrictedCoefficientRep A j ⟶ B) (hφ : Function.Injective φ.hom)
    (c : G × G → A) (b : H → B) (bF : G → A)
    (hb : ∀ g, φ.hom (bF (j g)) = b g)
    (hc : ∀ g h, φ.hom (c (j g, j h)) = B.ρ g (b h) - b (g * h) + b g) :
    ∀ g h, c (g, h) = A.ρ g (bF h) - bF (g * h) + bF g := by
  intro g h
  obtain ⟨g', rfl⟩ := hj g
  obtain ⟨h', rfl⟩ := hj h
  apply hφ
  rw [map_add, map_sub]
  change φ.hom (c (j g', j h')) =
    φ.hom ((restrictedCoefficientRep A j).ρ g' (bF (j h'))) -
      φ.hom (bF (j g' * j h')) + φ.hom (bF (j g'))
  rw [Rep.hom_comm_apply φ, ← map_mul j, hb, hb, hb]
  exact hc g' h'

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  [TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E)]
  [DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E)]
  [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

local instance : @ContinuousSMul ℤ (arithmeticSUnitFiniteStageRep K Ω a ha E)
    (arithmeticSUnitFiniteStageRep K Ω a ha E).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance : @ContinuousSMul ℤ (originalArithmeticSUnitRepresentation K Ω a ha)
    (originalArithmeticSUnitRepresentation K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Vanishing of an actual inflated S-unit H2 class is detected at a larger genuine finite Galois stage by descent of its original continuous S-unit witness. -/
theorem arithmeticSUnitContinuousH2_zero_detected_at_finiteStage
    (x : ArithmeticSUnitFiniteStageH2 K Ω a ha E)
    (hx : arithmeticSUnitFiniteStageH2Inflation K Ω a ha E x = 0) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hEF : E ≤ F,
        letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
        letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
        arithmeticSUnitFiniteTowerH2Inflation K Ω a ha E F hEF x = 0 := by
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois K Γ := originalUnramifiedGaloisUnion_isGalois a
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk _ = 0 at hx
    have hbmem := (Submodule.Quotient.mk_eq_zero _).mp hx
    let b := hbmem.choose
    have hb := hbmem.choose_spec
    have hdescent := arithmeticSUnitCochain_exists_finite_descent K Ω a ha E b
    let F := hdescent.choose
    have hEF := hdescent.choose_spec.1
    let f := hdescent.choose_spec.2.choose
    have hf := hdescent.choose_spec.2.choose_spec
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    haveI : IsScalarTower E F Γ := .of_algebraMap_eq' rfl
    letI : TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⊥
    letI : DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F) := ⟨rfl⟩
    letI : @ContinuousSMul ℤ (arithmeticSUnitFiniteStageRep K Ω a ha F)
        (arithmeticSUnitFiniteStageRep K Ω a ha F).hV2.toSMul inferInstance inferInstance :=
      ⟨continuous_of_discreteTopology⟩
    let cF := arithmeticSUnitFiniteTowerCocycleInflation K Ω a ha E F hEF c
    let φ := arithmeticSUnitFiniteStageInclusion K Ω a ha F
    let j : Gal(Γ/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
    let bF : C(Gal(F/K), arithmeticSUnitFiniteStageRep K Ω a ha F) :=
      ⟨fun g => Additive.ofMul (f g), continuous_of_discreteTopology⟩
    have hφ : Function.Injective φ.hom := by
      intro u v huv
      apply Additive.toMul.injective
      apply arithmeticSUnitFiniteStageUnitMap_injective K Ω a ha F
      exact congrArg Additive.toMul huv
    have hbF : ∀ g, φ.hom (bF (j g)) = b g := by
      intro g
      exact congrArg Additive.ofMul (hf g)
    have hcF : ∀ g h : Gal(Γ/K), φ.hom (cF.val (j g, j h)) =
        (originalArithmeticSUnitRepresentation K Ω a ha).ρ g (b h) - b (g * h) + b g := by
      intro g h
      have he : φ.hom (cF.val (j g, j h)) =
          (arithmeticSUnitFiniteStageInclusion K Ω a ha E).hom
            (c.val (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) := by
        apply Additive.toMul.injective
        change arithmeticSUnitFiniteStageUnitMap K Ω a ha F
            (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF
              (c.val (AlgEquiv.restrictNormalHom E (j g),
                AlgEquiv.restrictNormalHom E (j h))).toMul) =
          arithmeticSUnitFiniteStageUnitMap K Ω a ha E
            (c.val (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)).toMul
        have hz : (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h) =
            (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F g),
              AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F h)) := Prod.ext
          (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F g)
          (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F h)
        exact (arithmeticSUnitFiniteTransitionMap_global K Ω a ha E F hEF _).trans
          (congrArg (fun w : Gal(E/K) × Gal(E/K) =>
            arithmeticSUnitFiniteStageUnitMap K Ω a ha E (c.val w).toMul) hz.symm)
      exact he.trans (congrArg (fun d : continuousRepresentationCocyclesTwo
        (originalArithmeticSUnitRepresentation K Ω a ha) => d.val (g, h)) hb).symm
    have hc := coboundary_reflection (arithmeticSUnitFiniteStageRep K Ω a ha F)
      (originalArithmeticSUnitRepresentation K Ω a ha) j
      (AlgEquiv.restrictNormalHom_surjective Γ) φ hφ cF.val b bF hbF hcF
    refine ⟨F, hEF, ?_⟩
    change Submodule.Quotient.mk cF = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨bF, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact (hc z.1 z.2).symm

end
end Dubon2026
