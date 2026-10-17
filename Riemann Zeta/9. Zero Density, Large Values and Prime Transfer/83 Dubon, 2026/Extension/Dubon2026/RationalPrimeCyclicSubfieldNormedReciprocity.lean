import Dubon2026.RationalPrimeChangedCyclotomicClosureNaturalAction
import Dubon2026.LocalFieldCyclicSubfieldNormedUniformizer

/-! # Original changed-uniformizer reciprocity on cyclic cyclotomic subfields

The original normed uniformizer and its unramified upper extension already
exist for every prime. Applying finite cyclic reciprocity to the actual
subfield removes the odd-prime restriction without assuming the whole
cyclotomic field cyclic. This is the ramified local step toward the
conductor-two principal product, invariant sum and DUB-17 class generator.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

variable
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (L₀ : FiniteGaloisIntermediateField (rationalPrimeLocalField p hp)
      (rationalPrimeLocalClosure p hp))
    (hL₀ : L₀.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L₀/rationalPrimeLocalField p hp)]
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha))]

/-- The constructed normed uniformizer has its literal restricted Frobenius
image on every cyclic subfield, including at the prime two. -/
theorem rationalPrimeChangedCyclotomicClosure_cyclicSubfield_reciprocity_natural_mul_prime :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
    let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
    let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
    let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
    let i₀ : L₀ →ₐ[K] L := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    ∃ (_ : Algebra.FormallyUnramified 𝒪[E] 𝒪[M]),
    (localFieldFiniteCyclicReciprocity K Ω L₀
      (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit p hp a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i₀
            (embeddedNormalGaloisRestriction (F := E) j
              (localFieldArithmeticFrobenius E M)) := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
  let j := rationalPrimeOriginalCyclotomicClosureInclusion p hp n a u hu ha
  let i₀ : L₀ →ₐ[K] L := IntermediateField.inclusion hL₀
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) := ⟨rfl⟩
  exact localFieldFiniteCyclicReciprocity_of_norm_uniformizer_embedded_subfield
    K Ω E L₀ L M i₀ j (fun _ => rfl) (fun _ => rfl) (rationalPrimeNaturalMulPrimeUnit p hp a ha)
    (rationalPrimeChangedCyclotomicClosure_exists_integer_uniformizer p hp n a u hu ha)

end
end Dubon2026
