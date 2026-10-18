import Dubon2026.RationalPrimeTraceUnitCup

/-! Exact normalized local invariant of the actual coefficient-first relation
cup. This is the local summand comparison used by DUB-17 reverse localization. -/

namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.addCommGroup Submodule.module

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (σ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    Matrix.GeneralLinearGroup ι (ZMod q)) (hσ : Continuous σ)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  [TopologicalSpace (rationalPrimeTraceUnitHomRep p hp q σ)]
  [DiscreteTopology (rationalPrimeTraceUnitHomRep p hp q σ)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]

local instance traceInvariantHomContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceUnitHomRep p hp q σ)
      (rationalPrimeTraceUnitHomRep p hp q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance traceInvariantUnitsContinuousSMul :
    @ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The canonical unit invariant of the actual relation cup is minus the normalized scalar trace cup. -/
theorem rationalPrimeTraceUnitEvaluationCup_invariant
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
      (rationalPrimeLocalClosure p hp)
      (rationalPrimeTraceUnitEvaluationCup p hp q σ hσ hn
        (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y)
        (rationalPrimeTraceUnitH1Equiv p hp q σ hσ hn x)) =
    -rationalCyclicInvariant q (rationalPrimeTraceH1ScalarCup p hp q σ hσ x y) := by
  let inv := localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)
  refine (congrArg inv
    (rationalPrimeTraceUnitEvaluationCup_eq_neg_trace p hp q σ hσ hn x y)).trans ?_
  refine (map_neg inv _).trans ?_
  exact congrArg Neg.neg (rationalPrimeCyclotomicH2ScalarEquiv_invariant p hp q
    (matrixTraceZeroCharacterH1Cup σ hσ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous x y)).symm

end
end Dubon2026
