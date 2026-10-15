import Dubon2026.ArithmeticSUnitFiniteStageH2
import Dubon2026.ArithmeticSUnitFiniteTransitions

/-! # Literal finite-stage transitions for arithmetic S-unit H2

The original coefficient maps and actual Galois restrictions induce the
finite-stage cohomology maps. Their compatibility with the original global
inflation is needed for the S-unit coefficient colimit in the DUB-17 duality route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (hEF : E ≤ F)
  [TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha E)]
  [DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha E)]
  [TopologicalSpace (arithmeticSUnitFiniteStageRep K Ω a ha F)]
  [DiscreteTopology (arithmeticSUnitFiniteStageRep K Ω a ha F)]

local instance : @ContinuousSMul ℤ (arithmeticSUnitFiniteStageRep K Ω a ha E)
    (arithmeticSUnitFiniteStageRep K Ω a ha E).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance : @ContinuousSMul ℤ (arithmeticSUnitFiniteStageRep K Ω a ha F)
    (arithmeticSUnitFiniteStageRep K Ω a ha F).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Original restriction followed by the actual finite S-unit coefficient transition. -/
def arithmeticSUnitFiniteTowerCocycleInflation :
    continuousRepresentationCocyclesTwo (arithmeticSUnitFiniteStageRep K Ω a ha E) →ₗ[ℤ]
      continuousRepresentationCocyclesTwo (arithmeticSUnitFiniteStageRep K Ω a ha F) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  exact (continuousCoefficientCocycleTwoMap
    (restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha E)
      (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)))
    (arithmeticSUnitFiniteStageRep K Ω a ha F)
    (arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF).hom.toLinearMap
    continuous_of_discreteTopology
    (Rep.hom_comm_apply (arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF))).comp
      (continuousRepresentationCocycleTwoRestriction (arithmeticSUnitFiniteStageRep K Ω a ha E)
        (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)) continuous_of_discreteTopology)

/-- Actual finite-stage S-unit inflation on the original continuous cohomology quotients. -/
def arithmeticSUnitFiniteTowerH2Inflation :
    ArithmeticSUnitFiniteStageH2 K Ω a ha E →ₗ[ℤ]
      ArithmeticSUnitFiniteStageH2 K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  let j : Gal(F/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hj : Continuous j := continuous_of_discreteTopology
  let φ := (arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF).hom.toLinearMap
  let hE := arithmeticSUnitFiniteStageAction_continuous K Ω a ha E
  let hF := arithmeticSUnitFiniteStageAction_continuous K Ω a ha F
  exact (continuousCoefficientH2Map
    (restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha E) j)
    (arithmeticSUnitFiniteStageRep K Ω a ha F) φ continuous_of_discreteTopology
    (Rep.hom_comm_apply (arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF))
    (restrictedCoefficientAction_continuous (arithmeticSUnitFiniteStageRep K Ω a ha E) j hj hE)
    hF).comp (continuousRepresentationH2Restriction (arithmeticSUnitFiniteStageRep K Ω a ha E) hE j hj)

/-- The finite-stage map preserves the literal inflated representative. -/
theorem arithmeticSUnitFiniteTowerH2Inflation_mk
    (c : continuousRepresentationCocyclesTwo (arithmeticSUnitFiniteStageRep K Ω a ha E)) :
    arithmeticSUnitFiniteTowerH2Inflation K Ω a ha E F hEF (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (arithmeticSUnitFiniteTowerCocycleInflation K Ω a ha E F hEF c) := rfl

/-- Inflating directly to the original arithmetic coefficient agrees with inflation through a larger genuine finite stage. -/
theorem arithmeticSUnitFiniteStageH2Inflation_tower
    [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
    [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]
    (x : ArithmeticSUnitFiniteStageH2 K Ω a ha E) :
    arithmeticSUnitFiniteStageH2Inflation K Ω a ha E x =
      arithmeticSUnitFiniteStageH2Inflation K Ω a ha F
        (arithmeticSUnitFiniteTowerH2Inflation K Ω a ha E F hEF x) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower E F (originalUnramifiedGaloisUnion (Ω := Ω) a) := .of_algebraMap_eq' rfl
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    apply Additive.toMul.injective
    change arithmeticSUnitFiniteStageUnitMap K Ω a ha E
        (c.val (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2)).toMul =
      arithmeticSUnitFiniteStageUnitMap K Ω a ha F
        (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF
          (c.val (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.1),
            AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.2))).toMul)
    have hz : (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2) =
        (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.1),
          AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F z.2)) := Prod.ext
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F z.1)
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F z.2)
    exact (arithmeticSUnitFiniteTransitionMap_global K Ω a ha E F hEF
      (c.val (AlgEquiv.restrictNormalHom E z.1, AlgEquiv.restrictNormalHom E z.2)).toMul).symm.trans
        (congrArg (fun w : Gal(E/K) × Gal(E/K) => arithmeticSUnitFiniteStageUnitMap K Ω a ha F
          (arithmeticSUnitFiniteTransitionMap K Ω a ha E F hEF (c.val w).toMul)) hz)

end
end Dubon2026
