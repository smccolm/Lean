import Dubon2026.ArithmeticCoherentLocalInvariant

/-! # Perfect original local H1 pairings with coherent global normalization

Use the proved actual local duality with the image of the same global root.
This gives the pairing entering DUB-17's global duality maps without either
assuming perfectness or identifying unrelated local normalization choices.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero

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
  (A : Rep.{0} (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))

/-- The original character-dual cup normalized by the local image of
the actual chosen global root, on its unchanged continuous H1 spaces. -/
def rationalArithmeticLocalH1ScalarCup :
    let χ := rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)
    ContinuousRepresentationH1 A hA →ₗ[ZMod q]
      ContinuousRepresentationH1 (characterDualCoefficientRep A χ.toMonoidHom)
        (finiteCharacterDualAction_continuous A χ.toMonoidHom hA χ.continuous) →ₗ[ZMod q] ZMod q :=
  (continuousCharacterDualH1Cup A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous hA).compr₂
      (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp).toLinearMap

/-- The coherently normalized original local pairing is perfect by the
already proved local duality and the constructed compatible root map. -/
theorem rationalArithmeticLocalH1ScalarCup_isPerfPair :
    (rationalArithmeticLocalH1ScalarCup a q hqa p hp A hA).IsPerfPair := by
  exact localCharacterDualH1ScalarCup_isPerfPair
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp)
    (rationalArithmeticLocalRootCoefficientEquiv_equivariant a q hqa p hp) A hA
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

end
end Dubon2026
