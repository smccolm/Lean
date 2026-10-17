import Dubon2026.RationalPrimeEmbeddedCyclotomicFrobenius
import Dubon2026.RationalPrimeCyclicSubfieldNormedReciprocity
import Dubon2026.RationalTwoCyclicSubfieldPrimeCancellation

/-! # Inverse-unit action on the constructed two-primary cyclic subfield

The actual changed-uniformizer norm supplies Frobenius, the prime-two norm
cancels its prime factor, and the native root calculation identifies the
inverse unit. The same full-field automorphism restricts to the given
cyclic subfield. This advances the conductor-two principal-product input
to DUB-17's invariant-sum and full-order class construction.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable
    (n a b : ℕ) (hn : 1 ≤ n)
    (u : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hu : u.val = a) (ha : ¬2 ∣ a)
    (hcoprimeA : a.Coprime (2 ^ (n + 1)))
    (hcoprimeB : b.Coprime (2 ^ (n + 1))) (hab : a * b ≡ 1 [MOD 2 ^ (n + 1)])
    (L₀ : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL₀ : L₀.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha).toIntermediateField)
    [IsCyclic Gal(L₀/rationalPrimeLocalField 2 Nat.prime_two)]
    [FiniteDimensional (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField 2 Nat.prime_two)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha))]
    [ValuativeRel (rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha)]
    [(ValuativeRel.valuation (rationalPrimeLocalField 2 Nat.prime_two)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha))]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha))]

include hn hcoprimeA hcoprimeB hab

/-- The original normed action, supplied later by the actual auxiliary
field, combines with the proved root value and prime cancellation. -/
private theorem twoPrimaryNaturalAction_of_normed
    [Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha]
      𝒪[rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha]]
    (hrec :
      let K := rationalPrimeLocalField 2 Nat.prime_two
      let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
      let E := rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha
      let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
      let M := rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha
      let i₀ : L₀ →ₐ[K] F := IntermediateField.inclusion hL₀
      let j := rationalPrimeOriginalCyclotomicClosureInclusion 2 Nat.prime_two n a u hu ha
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
      (localFieldFiniteCyclicReciprocity K Ω L₀
        (Additive.ofMul (rationalPrimeNaturalMulPrimeUnit 2 Nat.prime_two a ha))).toMul =
        embeddedNormalGaloisRestriction (F := K) i₀
          (embeddedNormalGaloisRestriction (F := E) j (localFieldArithmeticFrobenius E M))) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
    let i₀ : L₀ →ₐ[K] F := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha
    ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
      (localFieldFiniteCyclicReciprocity K Ω L₀
        (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
        embeddedNormalGaloisRestriction (F := K) i₀ σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let E := rationalPrimeChangedAuxiliaryClosureField 2 Nat.prime_two n a u hu ha
  let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum 2 Nat.prime_two n a u hu ha
  let j := rationalPrimeOriginalCyclotomicClosureInclusion 2 Nat.prime_two n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let σ : Gal(F/K) := embeddedNormalGaloisRestriction (F := E) j
    (localFieldArithmeticFrobenius E M)
  refine ⟨σ, ?_, ?_⟩
  · exact rationalPrimeChangedCyclotomicClosure_embeddedFrobenius_root
      2 Nat.prime_two n a b u hu ha hcoprimeA hcoprimeB hab
  · exact (rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_mul_prime_eq_natural
      n a hn u hu ha L₀ hL₀).symm.trans hrec

/-- The original reciprocity of the natural unit on the cyclic subfield
is the restriction of an actual cyclotomic automorphism with inverse-unit
root exponent. All norm and prime-cancellation witnesses are derived. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_exists_natural_action :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
    let i₀ : L₀ →ₐ[K] F := IntermediateField.inclusion hL₀
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha
    ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
      (localFieldFiniteCyclicReciprocity K Ω L₀
        (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
        embeddedNormalGaloisRestriction (F := K) i₀ σ := by
  obtain ⟨hunram, hrec⟩ :=
    rationalPrimeChangedCyclotomicClosure_cyclicSubfield_reciprocity_natural_mul_prime
      2 Nat.prime_two n a u hu ha L₀ hL₀
  letI := hunram
  exact twoPrimaryNaturalAction_of_normed n a b hn u hu ha hcoprimeA hcoprimeB hab L₀ hL₀ hrec

end
end Dubon2026
