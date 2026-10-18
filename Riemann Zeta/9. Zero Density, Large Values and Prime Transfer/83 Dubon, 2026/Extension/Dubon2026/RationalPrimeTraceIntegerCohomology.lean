import Dubon2026.RationalPrimeTraceUnitCartierDuality
import Dubon2026.TraceZeroCharacterCohomologyCup
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv

/-! The literal prime-local deformation H1 with its integer coefficient
structure. This supplies the first input of the original relation cup; the
coefficient conversion retains the original matrix cocycles and boundaries. -/

namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.addCommGroup Submodule.module

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (σ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    Matrix.GeneralLinearGroup ι (ZMod q)) (hσ : Continuous σ)

/-- Retain the topology of the original matrix coefficient module. -/
instance rationalPrimeTraceIntegerTopology :
    TopologicalSpace (rationalPrimeTraceZeroIntegerRep p hp q σ) :=
  inferInstanceAs (TopologicalSpace (matrixTraceZeroAdjointRep σ))

/-- The original finite matrix coefficient topology is discrete. -/
instance rationalPrimeTraceIntegerDiscrete :
    DiscreteTopology (rationalPrimeTraceZeroIntegerRep p hp q σ) :=
  inferInstanceAs (DiscreteTopology (matrixTraceZeroAdjointRep σ))

local instance primeTraceIntegerContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (rationalPrimeTraceZeroIntegerRep p hp q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

include hσ in
/-- The same local matrix action is continuous on the original discrete integer coefficients. -/
theorem rationalPrimeTraceIntegerAction_continuous :
    Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ×
      rationalPrimeTraceZeroIntegerRep p hp q σ =>
        (rationalPrimeTraceZeroIntegerRep p hp q σ).ρ z.1 z.2) := by
  exact matrixTraceZeroAdjointAction_continuous σ hσ

/-- The original general continuous matrix H1 retains its literal representatives over the integers. -/
def rationalPrimeTraceIntegerGeneralH1Equiv :
    ContinuousRepresentationH1 (matrixTraceZeroAdjointRep σ)
      (matrixTraceZeroAdjointAction_continuous σ hσ) ≃+
    ContinuousRepresentationH1 (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (rationalPrimeTraceIntegerAction_continuous p hp q σ hσ) :=
  continuousH1AdditiveCoefficientEquiv (matrixTraceZeroAdjointRep σ)
    (rationalPrimeTraceZeroIntegerRep p hp q σ) (AddEquiv.refl _)
    continuous_of_discreteTopology continuous_of_discreteTopology (fun _ _ => rfl) _ _

/-- The exact local deformation quotient supplies the first input of the integer-linear relation cup. -/
def rationalPrimeTraceIntegerH1Equiv :
    ContinuousTraceZeroAdjointH1 σ hσ ≃+
    ContinuousRepresentationH1 (rationalPrimeTraceZeroIntegerRep p hp q σ)
      (rationalPrimeTraceIntegerAction_continuous p hp q σ hσ) :=
  (continuousTraceZeroH1GeneralEquiv σ hσ).toAddEquiv.trans
    (rationalPrimeTraceIntegerGeneralH1Equiv p hp q σ hσ)

end
end Dubon2026
