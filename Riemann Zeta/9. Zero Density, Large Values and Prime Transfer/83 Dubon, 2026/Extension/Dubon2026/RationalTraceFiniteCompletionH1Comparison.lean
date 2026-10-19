import Dubon2026.RationalTraceFiniteLocalHomH1
import Dubon2026.RationalTraceOriginalLocalHomH1
import Dubon2026.RationalArithmeticOriginalCompletionHomMap
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! The two original local H1 identifications equal the actual completion
map used by the dual connecting diagram. This identifies the maps, not
just their domains, on DUB-17's prescribed local-class recovery chain. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois


variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)



attribute [local instance] finiteLocalTraceCoefficientFinite
  finiteLocalTraceCoefficientModuleFinite finiteLocalTraceHomTopology
  finiteLocalTraceHomDiscrete finiteLocalTraceHomContinuousSMul
  finiteLocalPrimeHomTopology finiteLocalPrimeHomDiscrete finiteLocalPrimeHomContinuousSMul
attribute [local instance] traceOriginalFiniteRepFinite
  traceCartierOriginalHomTopology traceCartierOriginalHomDiscrete
  traceOriginalSourceHomContinuousSMul traceOriginalTargetHomTopology
  traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul

variable (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)

/-- The exact finite trace and original completion H1 comparison square. -/
abbrev RationalTraceFiniteCompletionH1Comparison : Prop :=
    let B := rationalTraceOriginalFiniteRep a q σ F hker
    let A := rationalTraceFiniteLocalHomRep a q σ F hker p hp
    let C := rationalTraceOriginalLocalHomRep a q σ F hker p hp
    let j := (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
    let hj := rationalOriginalCompletionGaloisEquiv_symm_continuous p hp
    let m := rationalArithmeticOriginalCompletionHomMap a F p hp B
    let hA := arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp
    let hC := rationalTraceOriginalLocalHomAction_continuous a q σ F hker p hp
    ∀ x : RationalTraceFiniteLocalHomH1 a q σ F hker p hp,
    rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn
      (rationalTraceFiniteLocalHomH1Equiv a q σ F hker p hp hσ hn x) =
    continuousCoefficientH1Map (restrictedCoefficientRep A j) C m.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply m)
      (restrictedCoefficientAction_continuous A j hj hA) hC
      (continuousRepresentationH1Restriction A hA j hj x)

/-- The literal finite coefficient identification and completion H1
equivalence compose to the actual map of the dual connecting diagram. -/
theorem rationalTraceFiniteCompletionH1_comparison :
    RationalTraceFiniteCompletionH1Comparison a q σ F hker p hp hσ hn := by
  let B := rationalTraceOriginalFiniteRep a q σ F hker
  let A := rationalTraceFiniteLocalHomRep a q σ F hker p hp
  let C := rationalTraceOriginalLocalHomRep a q σ F hker p hp
  let j := (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom
  let hj := rationalOriginalCompletionGaloisEquiv_symm_continuous p hp
  let m := rationalArithmeticOriginalCompletionHomMap a F p hp B
  let hA := arithmeticPrimeRestrictedUnitHomAction_continuous a F B p hp
  let hC := rationalTraceOriginalLocalHomAction_continuous a q σ F hker p hp
  change ∀ x : RationalTraceFiniteLocalHomH1 a q σ F hker p hp, _
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let c' := continuousCocycleOneAdditiveEquiv _ _
      (rationalTraceFiniteLocalHomCoefficientEquiv a q σ F hker p hp)
      continuous_of_discreteTopology continuous_of_discreteTopology
      (rationalTraceFiniteLocalHomCoefficientEquiv_equivariant a q σ F hker p hp) c
    refine (congrArg (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn)
      (rationalTraceFiniteLocalHomH1Equiv_mk a q σ F hker p hp hσ hn c)).trans ?_
    refine (rationalTraceOriginalLocalHomH1Equiv_mk a q σ F hker p hp hσ hn c').trans ?_
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact rationalTraceOriginalLocalHomCocycleMap_apply a q σ F hker p hp c' g

end
end Dubon2026
