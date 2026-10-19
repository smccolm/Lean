import Dubon2026.RationalPrimeTraceUnitCupInvariant
import Dubon2026.RationalPrimeTraceCupPerfect

/-! The repository's proved perfect trace pairing detects the actual
local unit-Hom H1 class. This is the separation step for DUB-17's retained
source-local cup identities; perfectness is proved, not supplied. -/
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

local instance localRecoveryUnitHomContinuousSMul :
    @ContinuousSMul ℤ (rationalPrimeTraceUnitHomRep p hp q σ)
      (rationalPrimeTraceUnitHomRep p hp q σ).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
local instance localRecoveryUnitsContinuousSMul :
    @ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))
      (Rep.ofAlgebraAutOnUnits (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Equality of every original local evaluation cup determines the
original unit-Hom H1 class, using the proved trace normalization and
perfectness with only the genuine nonzero-dimension condition. -/
theorem rationalPrimeTraceUnitH1_eq_of_evaluation_cups
    (u v : ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q σ)
      (rationalPrimeTraceUnitHomAction_continuous p hp q σ hσ hn))
    (h : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalPrimeTraceUnitEvaluationCup p hp q σ hσ hn
        (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y) u =
      rationalPrimeTraceUnitEvaluationCup p hp q σ hσ hn
        (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y) v) : u = v := by
  let e := rationalPrimeTraceUnitH1Equiv p hp q σ hσ hn
  apply e.symm.injective
  apply (rationalPrimeTraceH1ScalarCup_isPerfPair p hp q σ hσ hn).bijective_left.injective
  apply LinearMap.ext
  intro y
  apply rationalCyclicInvariant_injective q
  apply neg_injective
  let inv := localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)
  have hu := rationalPrimeTraceUnitEvaluationCup_invariant p hp q σ hσ hn (e.symm u) y
  have hv := rationalPrimeTraceUnitEvaluationCup_invariant p hp q σ hσ hn (e.symm v) y
  have hc : rationalPrimeTraceUnitEvaluationCup p hp q σ hσ hn
      (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y) (e (e.symm u)) =
      rationalPrimeTraceUnitEvaluationCup p hp q σ hσ hn
        (rationalPrimeTraceIntegerH1Equiv p hp q σ hσ y) (e (e.symm v)) := by
    simpa only [e.apply_symm_apply] using h y
  exact hu.symm.trans ((congrArg inv hc).trans hv)

end
end Dubon2026
