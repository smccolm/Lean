import Dubon2026.LocalCharacterDualH1Perfect
import Dubon2026.RationalPrimeTrivialCharacterDualPerfect
import Dubon2026.RationalPrimeCyclotomicH2Scalar

/-! # Full prime-field local H1 duality at the original rational prime

The actual arithmetic cyclotomic character and proved root identification
supply the coefficient data for arbitrary finite continuous actions. This
removes the split-action and independent cyclotomic-data premises from the
prime-field local H1 input in DUB-17's trace-zero Selmer dependency chain.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))

/-- The original rational-prime character-dual cup is perfect for arbitrary
finite continuous prime-field coefficients. The actual field, cyclotomic character,
coefficient identification, H1 finiteness and both annihilators are supplied
by the existing arithmetic constructions and proved Kummer comparison. -/
theorem rationalPrimeCharacterDualH1ScalarCup_isPerfPair :
    (rationalPrimeCharacterDualH1ScalarCup p hp q A hA).IsPerfPair := by
  let χ := (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
  exact localCharacterDualH1ScalarCup_isPerfPair
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q χ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalPrimeCyclotomicRootCoefficientEquiv p hp q)
    (rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q) A hA
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

end
end Dubon2026
