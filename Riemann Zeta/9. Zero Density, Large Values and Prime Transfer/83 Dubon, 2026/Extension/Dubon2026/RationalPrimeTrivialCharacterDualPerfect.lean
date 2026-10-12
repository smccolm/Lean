import Dubon2026.LocalTrivialCharacterDualPerfect
import Dubon2026.RationalPrimeCyclotomicH2Scalar

/-! # The split local duality base case at the original rational prime

The actual arithmetic cyclotomic character and its already proved root
identification supply the coefficient data. This removes the independent
coefficient equivalence from the split case used by DUB-17's trace-duality route.
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

/-- The actual character-dual cup at the original rational prime, followed by
its original cyclotomic H2 invariant. -/
def rationalPrimeCharacterDualH1ScalarCup :
    ContinuousRepresentationH1 A hA →ₗ[ZMod q]
      ContinuousRepresentationH1 (characterDualCoefficientRep A
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
        (finiteCharacterDualAction_continuous A
          (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom hA
          (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) →ₗ[ZMod q] ZMod q :=
  (continuousCharacterDualH1Cup A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous hA).compr₂
      (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).toLinearMap

/-- The original rational-prime character-dual cup is perfect for split
finite prime-field coefficients. The actual field, cyclotomic character,
coefficient identification, H1 finiteness and both annihilators are supplied
by the existing arithmetic constructions and proved Kummer comparison. -/
theorem rationalPrimeTrivialCharacterDualH1ScalarCup_isPerfPair
    (htrivial : ∀ g a, A.ρ g a = a) :
    (rationalPrimeCharacterDualH1ScalarCup p hp q A hA).IsPerfPair := by
  let χ := (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
  let D₀ := characterDualCoefficientRep
    (coefficientCharacterRep (1 : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* ZMod q)) χ
  letI : TopologicalSpace D₀ := ⊥
  letI : DiscreteTopology D₀ := ⟨rfl⟩
  exact localTrivialCharacterDualH1ScalarCup_isPerfPair
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q χ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalPrimeCyclotomicRootCoefficientEquiv p hp q)
    (rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q) A htrivial hA
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

end
end Dubon2026
