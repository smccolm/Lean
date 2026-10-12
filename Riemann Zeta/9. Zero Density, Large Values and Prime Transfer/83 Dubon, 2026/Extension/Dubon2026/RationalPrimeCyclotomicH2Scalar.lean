import Dubon2026.RationalPrimeRootH2Invariant
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv
import Dubon2026.CyclotomicRootAdditiveEquiv
import Dubon2026.ArithmeticCyclotomicCoefficientCharacter
import Dubon2026.TraceZeroContinuousCharacterPairing
import Mathlib.Algebra.Module.ZMod

/-! # The actual prime-field cyclotomic H2 scalar target

Identify the original cyclotomic coefficient representation with actual roots of
unity and apply the original local invariant. This is the scalar target for the
arithmetic trace cup. Perfectness of the resulting H1 pairing remains separate.
-/

namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]


/-- The literal original cyclotomic coefficient group is additively the actual
root-of-unity group, via a primitive root in the actual local algebraic closure. -/
def rationalPrimeCyclotomicRootCoefficientEquiv :
    coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom ≃+
        galoisRootOfUnityRepresentation
          (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q :=
  (primitiveRootAdditiveEquiv
    (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot (rationalPrimeLocalClosure p hp) q))).trans
        Rep.toAdditive.symm

/-- The identification retains the actual cyclotomic automorphism action. -/
theorem rationalPrimeCyclotomicRootCoefficientEquiv_equivariant
    (g : rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
      rationalPrimeLocalClosure p hp) (x : ZMod q) :
    rationalPrimeCyclotomicRootCoefficientEquiv p hp q
      ((coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).ρ g x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
          (rationalPrimeCyclotomicRootCoefficientEquiv p hp q x) := by
  let hμ := Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot (rationalPrimeLocalClosure p hp) q)
  apply Rep.toAdditive.injective
  change primitiveRootAdditiveEquiv hμ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q) g * x) =
    Additive.ofMul (g • Additive.toMul (primitiveRootAdditiveEquiv hμ x))
  have hc : rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q) g =
      (hμ.autToPow (rationalPrimeLocalField p hp) g : ZMod q) := by
    change ZMod.castHom (dvd_refl q) (ZMod q)
      (hμ.autToPow (rationalPrimeLocalField p hp) g : ZMod q) = _
    simp
  rw [hc]
  exact (congrArg Additive.ofMul (primitiveRootAdditiveEquiv_galois hμ g x)).symm

variable
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The same genuine coefficient identification transports the actual continuous
cyclotomic H2 into the original root-of-unity H2. -/
def rationalPrimeCyclotomicH2RootEquiv :
    ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) ≃+
      GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
        (Ω := rationalPrimeLocalClosure p hp) q :=
  continuousH2AdditiveCoefficientEquiv _ _
    (rationalPrimeCyclotomicRootCoefficientEquiv p hp q)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q) _ _

/-- The actual prime-field cyclotomic H2 is the original prime field, by Kummer
exactness and the full invariant. No dimension or perfectness certificate is assumed. -/
def rationalPrimeCyclotomicH2ScalarEquiv :
    ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) ≃+
      ZMod q :=
  (rationalPrimeCyclotomicH2RootEquiv p hp q).trans
    (rationalPrimeRootH2CyclicEquiv p hp q).toAddEquiv

/-- The original scalar identification is linear for the actual coefficient
prime field, so it can be composed with the bilinear arithmetic cup. -/
def rationalPrimeCyclotomicH2ScalarLinearEquiv :
    ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) ≃ₗ[ZMod q]
      ZMod q :=
  { rationalPrimeCyclotomicH2ScalarEquiv p hp q with
    map_smul' := ZMod.map_smul (rationalPrimeCyclotomicH2ScalarEquiv p hp q) }

/-- The scalar coordinate is normalized by the actual full local invariant of
the actual transported Kummer class. -/
theorem rationalPrimeCyclotomicH2ScalarEquiv_invariant
    (x : ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)) :
    rationalCyclicInvariant q (rationalPrimeCyclotomicH2ScalarEquiv p hp q x) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
          (Ω := rationalPrimeLocalClosure p hp) q
          (rationalPrimeCyclotomicH2RootEquiv p hp q x)) :=
  rationalPrimeRootH2CyclicEquiv_invariant p hp q
    (rationalPrimeCyclotomicH2RootEquiv p hp q x)

end
end Dubon2026
