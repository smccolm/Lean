import Dubon2026.ArithmeticUnitH2Restriction
import Dubon2026.RationalPrimeCharacterDualH1Perfect

/-! # Coherent local invariant coordinates for original global H2 classes

Each local scalar coordinate uses the image of a single actual global root.
Its value on restricted global classes is the genuine local unit invariant.
This is the normalization needed to apply a proved global reciprocity theorem
in DUB-17's Selmer chain; it does not assume or prove that global theorem.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticGlobalRootContinuousSMul arithmeticGlobalUnitContinuousSMul
  characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- Normalize the original local cyclotomic H2 through the image of the
single chosen global primitive root and the genuine local invariant. -/
def rationalArithmeticLocalH2ScalarEquiv :
    ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) ≃ₗ[ZMod q] ZMod q :=
  localCharacterLineH2ScalarEquiv
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp)
    (rationalArithmeticLocalRootCoefficientEquiv_equivariant a q hqa p hp)

variable [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- On every original global cyclotomic H2 class, the coherently normalized
scalar is exactly the local invariant of the restricted global Kummer class. -/
theorem rationalArithmeticLocalH2ScalarEquiv_global_invariant
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
      (rationalPrimeCyclotomicH2Restriction a q hqa p hp x)) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalArithmeticUnitH2Restriction a p hp
          (rationalArithmeticKummerH2Inclusion a q
            (rationalArithmeticCyclotomicH2RootEquiv a q hqa x))) := by
  let I := localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp)
  let K := galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
    (Ω := rationalPrimeLocalClosure p hp) q
  have he := rationalArithmeticRootH2Restriction_compatible a q hqa p hp x
  have hk := rationalArithmeticUnitH2Restriction_kummer a p hp q hqa
    (rationalArithmeticCyclotomicH2RootEquiv a q hqa x)
  exact (rationalPrimeRootH2CyclicEquiv_invariant p hp q
    (rationalArithmeticLocalCyclotomicH2RootEquiv a q hqa p hp
      (rationalPrimeCyclotomicH2Restriction a q hqa p hp x))).trans
        ((congrArg I hk).trans (congrArg (fun z => I (K z)) he)).symm

end
end Dubon2026
