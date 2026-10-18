import Dubon2026.RationalPrimeTraceUnitCohomology
import Dubon2026.RationalPrimeTraceIntegerCohomology
import Dubon2026.OriginalInternalHomEvaluation
import Dubon2026.ContinuousCupSkewSymmetry
import Dubon2026.RationalPrimeTraceCupInvariant

/-! The exact local comparison needed by the finite relation total. The
original coefficient-first evaluation cup is the negative of the original
dual-first trace cup, through the same Kummer inclusion and root normalization. -/

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

local instance traceCupIntegerContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (rationalPrimeTraceZeroIntegerRep p hp q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance traceCupHomContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceUnitHomRep p hp q σ)
      (rationalPrimeTraceUnitHomRep p hp q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance traceCupUnitsContinuousSMul :
    @ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The original coefficient-first local relation cup on the actual trace coefficients. -/
def rationalPrimeTraceUnitEvaluationCup :=
  continuousH1Cup (rationalPrimeTraceZeroIntegerRep p hp q σ)
    (rationalPrimeTraceUnitHomRep p hp q σ)
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
    (originalInternalHomEvaluation (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)))
    (originalInternalHomEvaluation_equivariant (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)))
    continuous_of_discreteTopology (rationalPrimeTraceIntegerAction_continuous p hp q σ hσ)
    (rationalPrimeTraceUnitHomAction_continuous p hp q σ hσ hn)
    (discreteGaloisUnitAction_continuous
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp))

/-- The local Cartier map preserves the original cup, including its reversed-order sign. -/
theorem rationalPrimeTraceUnitEvaluationCup_eq_neg_trace
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalPrimeTraceUnitEvaluationCup p hp q σ hσ hn
      (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y)
      (rationalPrimeTraceUnitH1Equiv p hp q σ hσ hn x) =
    -galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q
      (rationalPrimeCyclotomicH2RootEquiv p hp q
        (matrixTraceZeroCharacterH1Cup σ hσ
          (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
          (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous x y)) := by
  refine (continuousH1Cup_skew (rationalPrimeTraceZeroIntegerRep p hp q σ)
    (rationalPrimeTraceUnitHomRep p hp q σ)
    (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
    (originalInternalHomEvaluation (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)))
    (originalInternalHomEvaluation_equivariant (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)))
    continuous_of_discreteTopology (rationalPrimeTraceIntegerAction_continuous p hp q σ hσ)
    (rationalPrimeTraceUnitHomAction_continuous p hp q σ hσ hn)
    (discreteGaloisUnitAction_continuous
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp))
    (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y)
    (rationalPrimeTraceUnitH1Equiv p hp q σ hσ hn x)).trans ?_
  apply congrArg Neg.neg
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ d =>
      apply congrArg ((continuousRepresentationCoboundariesTwo
        (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
        (discreteGaloisUnitAction_continuous
          (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp))).mkQ)
      apply Subtype.ext
      apply Subtype.ext
      funext z
      exact rationalPrimeTraceUnitDualEquiv_apply p hp q σ hn (c.val z.1)
        (matrixTraceZeroAdjointRepresentation σ z.1 (d.val z.2))

end
end Dubon2026
