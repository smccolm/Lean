import Dubon2026.RationalPrimeFiniteScalarCyclotomicH2
import Dubon2026.LocalFiniteScalarCharacterDualPerfect

/-! # Actual arithmetic local duality for arbitrary finite coefficient fields

The genuine arithmetic character and root identification discharge all local
cyclotomic input hypotheses. The original H2 invariant then normalizes the
proved cup annihilators. This is the precise input to the original trace-zero
matrix pairing in DUB-17's Selmer dependency chain.
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

/-- The actual finite-field arithmetic character-dual cup, normalized by
the constructed scalar invariant on its original cyclotomic H2. -/
def rationalPrimeFiniteScalarCharacterDualH1Cup :
    ContinuousRepresentationH1 A hA →ₗ[k]
      ContinuousRepresentationH1 (characterDualCoefficientRep A
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
        (finiteCharacterDualAction_continuous A
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom hA
          (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous) →ₗ[k] k :=
  (continuousCharacterDualH1Cup A
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous hA).compr₂
      (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k).toLinearMap

/-- The actual arithmetic finite-field cup detects its left original H1
argument without a split-action or independent cyclotomic hypothesis. -/
theorem rationalPrimeFiniteScalarCharacterDualH1Cup_left_injective :
    Function.Injective (rationalPrimeFiniteScalarCharacterDualH1Cup p hp q A hA) := by
  let T := fun χ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* k =>
    (hχ : Continuous χ) → Function.Injective (continuousCharacterDualH1Cup A χ hχ hA)
  have hs : T ((algebraMap (ZMod q) k).toMonoidHom.comp
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom) := fun _ =>
    localFiniteScalarCharacterDualH1Cup_left_injective
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
      (rationalPrimeCyclotomicRootCoefficientEquiv p hp q)
      (rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q) A hA
      (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hi := (Eq.mp (congrArg T
    (rationalPrimeCyclotomicCoefficientCharacter_scalarExtension p hp q k)) hs)
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous
  intro x y h
  apply hi
  apply LinearMap.ext
  intro z
  exact (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k).injective (DFunLike.congr_fun h z)

/-- The same original arithmetic finite-field cup detects its right original
H1 argument using the proved field-trace comparison. -/
theorem rationalPrimeFiniteScalarCharacterDualH1Cup_right_injective :
    Function.Injective (rationalPrimeFiniteScalarCharacterDualH1Cup p hp q A hA).flip := by
  let T := fun χ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* k =>
    (hχ : Continuous χ) → ∀ (x y : ContinuousRepresentationH1 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ)),
      (∀ z, continuousCharacterDualH1Cup A χ hχ hA z x =
        continuousCharacterDualH1Cup A χ hχ hA z y) → x = y
  have hs : T ((algebraMap (ZMod q) k).toMonoidHom.comp
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom) := by
    intro hχ x y h
    apply localFiniteScalarCharacterDualH1Cup_right_injective
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
      (rationalPrimeCyclotomicRootCoefficientEquiv p hp q)
      (rationalPrimeCyclotomicRootCoefficientEquiv_equivariant p hp q) A hA
      (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    exact LinearMap.ext h
  have hi := (Eq.mp (congrArg T
    (rationalPrimeCyclotomicCoefficientCharacter_scalarExtension p hp q k)) hs)
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous
  intro x y h
  apply hi
  intro z
  exact (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k).injective (DFunLike.congr_fun h z)

/-- Original arithmetic local H1 duality is perfect for every finite
continuous representation over the original finite coefficient field. -/
theorem rationalPrimeFiniteScalarCharacterDualH1Cup_isPerfPair :
    (rationalPrimeFiniteScalarCharacterDualH1Cup p hp q A hA).IsPerfPair := by
  haveI := localField_finiteScalarCoefficientH1 q
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) A hA
    (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  haveI : Module.Finite k (ContinuousRepresentationH1 A hA) := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective
    (p := rationalPrimeFiniteScalarCharacterDualH1Cup p hp q A hA)
    (rationalPrimeFiniteScalarCharacterDualH1Cup_left_injective p hp q A hA)
    (rationalPrimeFiniteScalarCharacterDualH1Cup_right_injective p hp q A hA)

end
end Dubon2026
