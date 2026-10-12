import Dubon2026.LocalFieldFiniteScalarCoefficientH1
import Dubon2026.RationalPrimeRootH2Invariant
import Dubon2026.ArithmeticTraceZeroCohomologyCup

/-! # Finiteness of both original prime-local trace-cup domains

The actual rational prime completion and the actual cyclotomic character
specialize the finite-coefficient theorem to the two original H1 spaces in
DUB-17's trace-zero local duality dependency. No H1 finiteness, splitting field,
trivial action or matrix-dimension condition is assumed.
-/

namespace Dubon2026
noncomputable section
open Matrix

attribute [local instance] rationalPrimeLocalField_charZero

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime] [CharP k q]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι k) (hρ : Continuous ρ)

include q in
/-- The actual prime-local trace-zero deformation H1 is finite over the original
finite coefficient field, via its already proved exact quotient comparison. -/
theorem rationalPrimeTraceZeroAdjointH1_finite :
    Finite (ContinuousTraceZeroAdjointH1 ρ hρ) := by
  haveI := localField_finiteScalarCoefficientH1 q (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp) (matrixTraceZeroAdjointRep ρ)
    (matrixTraceZeroAdjointAction_continuous ρ hρ)
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  exact Finite.of_injective (continuousTraceZeroH1GeneralEquiv ρ hρ)
    (continuousTraceZeroH1GeneralEquiv ρ hρ).injective

/-- The actual cyclotomic-twisted prime-local trace-zero H1 is finite. Both the
character and its continuity are the existing arithmetic constructions. -/
theorem rationalPrimeCyclotomicTraceZeroH1_finite :
    Finite (ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ρ hρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)) := by
  exact localField_finiteScalarCoefficientH1 q (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)
    (matrixTraceZeroCharacterRep ρ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
    (matrixTraceZeroCharacterAction_continuous ρ hρ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

/-- Both domains of the original prime-local trace cup are finite. This
discharges finiteness, while nondegeneracy is a separate local duality obligation. -/
theorem rationalPrimeTraceCupDomains_finite :
    Finite (ContinuousTraceZeroAdjointH1 ρ hρ) ∧
      Finite (ContinuousRepresentationH1
        (matrixTraceZeroCharacterRep ρ
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
        (matrixTraceZeroCharacterAction_continuous ρ hρ
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)) :=
  ⟨rationalPrimeTraceZeroAdjointH1_finite p hp q ρ hρ,
    rationalPrimeCyclotomicTraceZeroH1_finite p hp q ρ hρ⟩

end
end Dubon2026
