import Dubon2026.RationalPrimeTraceCupInvariant
import Dubon2026.RationalPrimeCharacterDualH1Perfect
import Dubon2026.TraceZeroNormalizedH1Perfect
import Dubon2026.RationalPrimeTraceZeroH1Finite

/-! # Perfectness of the existing prime-field arithmetic trace cup

This exact consumer proves perfectness of the pre-existing arithmetic trace
cup, with its original invariant and original deformation H1 quotients.
It closes that local-duality input to DUB-17 without redefining the pairing.
-/

namespace Dubon2026
noncomputable section
open Matrix

attribute [local instance] characterDualSequenceContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)

/-- The exact existing scalar trace cup is perfect on the original local
deformation H1 spaces, assuming only the genuine nonzero matrix dimension. -/
theorem rationalPrimeTraceH1ScalarCup_isPerfPair
    (hn : (Fintype.card ι : ZMod q) ≠ 0) :
    (rationalPrimeTraceH1ScalarCup p hp q ρ hρ).IsPerfPair := by
  let χ := (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
  letI : TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ) := ⟨rfl⟩
  haveI := rationalPrimeTraceZeroAdjointH1_finite p hp q ρ hρ
  haveI : Module.Finite (ZMod q) (ContinuousTraceZeroAdjointH1 ρ hρ) := Module.Finite.of_finite
  exact matrixTraceZeroNormalizedH1Cup_isPerfPair ρ hρ χ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q) hn
    (rationalPrimeCharacterDualH1ScalarCup_isPerfPair p hp q
      (matrixTraceZeroAdjointRep ρ) (matrixTraceZeroAdjointAction_continuous ρ hρ))

end
end Dubon2026
