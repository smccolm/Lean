import Dubon2026.RationalPrimeFiniteScalarCyclotomicH2
import Dubon2026.LocalFiniteScalarCharacterDualH2Perfect

/-! # Actual finite-field local H0/H2 duality at the original rational prime

The arithmetic character equality and original scalar invariant discharge
all independent cyclotomic inputs. Both endpoint maps are bijective on the
original H2 and invariant spaces. This is the actual local endpoint used
before the global-duality/Selmer sequence in DUB-17's continuation route.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul rationalPrimeLocalField_charZero

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {k : Type} [Field k] [Finite k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (A : Rep.{0} k Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  [DiscreteTopology (characterDualCoefficientRep A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)]
  (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) × A =>
    A.ρ z.1 z.2))

/-- The original arithmetic dual H2/invariant pairing with its constructed
finite-field cyclotomic scalar invariant. -/
def rationalPrimeFiniteScalarCharacterDualH2Pairing :
    ContinuousRepresentationH2 (characterDualCoefficientRep A
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (finiteCharacterDualAction_continuous A
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom hA
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous) →ₗ[k]
      A.ρ.invariants →ₗ[k] k :=
  (continuousCharacterDualH2InvariantPairing A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous hA).compr₂
      (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k).toLinearMap

/-- The genuine arithmetic finite-field H0/H2 endpoint is perfect for
arbitrary finite actions. No endpoint, H2 dimension, finiteness or independent
cyclotomic-identification hypothesis is supplied. -/
theorem rationalPrimeFiniteScalarCharacterDualH2Pairing_isPerfPair :
    (rationalPrimeFiniteScalarCharacterDualH2Pairing p hp q A hA).IsPerfPair := by
  haveI : Module.Finite k A.ρ.invariants := Module.Finite.of_finite
  let T := fun χ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* k =>
    ∀ (hχ : Continuous χ) (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k),
      ((continuousCharacterDualH2InvariantPairing A χ hχ hA).compr₂ σ.toLinearMap).IsPerfPair
  have hs : T ((algebraMap (ZMod q) k).toMonoidHom.comp
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom) := by
    intro hχ σ
    let χq := (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    let hχq := (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
    let e := rationalPrimeCyclotomicRootCoefficientEquiv p hp q
    let he := rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q
    let τ := finiteScalarCharacterH2ScalarEquiv q χq hχq
      (localCharacterLineH2ScalarEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp) q χq hχq e he) (k := k)
    let P := localFiniteScalarCharacterDualH2InvariantPairing
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q χq hχq e he A hA
    haveI : P.IsPerfPair := localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q χq hχq e he A hA
      (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    apply LinearMap.IsPerfPair.of_injective'
    · intro x y h
      apply (LinearMap.IsPerfPair.bijective_left P).injective
      apply LinearMap.ext
      intro w
      exact congrArg τ (σ.injective (DFunLike.congr_fun h w))
    · intro x y h
      apply (LinearMap.IsPerfPair.bijective_right P).injective
      apply LinearMap.ext
      intro z
      exact congrArg τ (σ.injective (DFunLike.congr_fun h z))
  exact (Eq.mp (congrArg T
    (rationalPrimeCyclotomicCoefficientCharacter_scalarExtension p hp q k)) hs)
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous
      (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k)

end
end Dubon2026
