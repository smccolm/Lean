import Dubon2026.ArithmeticCoherentLocalInvariant
import Dubon2026.ArithmeticCyclotomicCupRestriction

/-! # The actual arithmetic trace cup and coherent local unit invariants

This consumes the existing trace-zero deformation restriction and its proved
cyclotomic cup naturality. The resulting local scalar is the local invariant
of the same global Kummer class. It is the precise input for reciprocity to
make global classes orthogonal in DUB-17's Selmer duality sequence.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q)) (hσ : Continuous σ)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- On the actual restricted global deformation classes, the coherently
normalized local trace cup is the genuine local invariant of the original
global Kummer cup class. The original negative trace-dual orientation and
both original restriction maps are retained. -/
theorem rationalArithmeticCoherentTraceCup_global_invariant
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let χP := rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
      (matrixTraceZeroCharacterH1Cup (σ.comp j.toMonoidHom) (hσ.comp j.continuous)
        χP.toMonoidHom χP.continuous
        (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y))) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa
              (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)))) := by
  have hc := rationalArithmeticTraceZeroH1Cup_prime_restriction a q hqa σ hσ p hp x y
  exact (congrArg (fun z => rationalCyclicInvariant q
    (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp z)) hc).symm.trans
      (rationalArithmeticLocalH2ScalarEquiv_global_invariant a q hqa p hp
        (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y))

end
end Dubon2026
