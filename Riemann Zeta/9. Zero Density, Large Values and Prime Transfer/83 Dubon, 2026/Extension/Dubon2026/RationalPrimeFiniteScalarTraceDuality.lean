import Dubon2026.RationalPrimeFiniteScalarCharacterDual
import Dubon2026.TraceZeroNormalizedH1Perfect
import Dubon2026.RationalPrimeTraceZeroH1Finite

/-! # Perfectness of the original finite-field arithmetic trace cup

All coefficient-duality and H1-finiteness inputs to the matrix comparison are
discharged by actual local arithmetic. Only the genuine trace-zero dimension
condition remains. This proves the local deformation pairing needed in the
global-duality and Selmer chain toward DUB-17's higher continuation theorem.
-/

namespace Dubon2026
noncomputable section
open Matrix

attribute [local instance] characterDualSequenceContinuousSMul

variable {ι k : Type} [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
    GeneralLinearGroup ι k) (hρ : Continuous ρ)

/-- The literal original finite-field trace cup with its constructed local
scalar invariant, retaining the original two deformation H1 spaces. -/
def rationalPrimeFiniteScalarTraceH1Cup :
    ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ρ hρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous) →ₗ[k]
      ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[k] k :=
  matrixTraceZeroNormalizedH1Cup ρ hρ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous
    (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k)

/-- The original finite-field local trace-zero pairing is perfect. Actual
coefficient duality, both original H1 spaces and their finiteness, the arithmetic
cyclotomic character and the H2 invariant are proved, not supplied as premises. -/
theorem rationalPrimeFiniteScalarTraceH1Cup_isPerfPair
    (hn : (Fintype.card ι : k) ≠ 0) :
    (rationalPrimeFiniteScalarTraceH1Cup p hp q ρ hρ).IsPerfPair := by
  let χ := (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
  letI : TopologicalSpace (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (matrixTraceZeroAdjointRep ρ) χ) := ⟨rfl⟩
  haveI := rationalPrimeTraceZeroAdjointH1_finite p hp q ρ hρ
  haveI : Module.Finite k (ContinuousTraceZeroAdjointH1 ρ hρ) := Module.Finite.of_finite
  exact matrixTraceZeroNormalizedH1Cup_isPerfPair ρ hρ χ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous
    (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k) hn
    (rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair p hp q
      (matrixTraceZeroAdjointRep ρ) (matrixTraceZeroAdjointAction_continuous ρ hρ))

end
end Dubon2026
