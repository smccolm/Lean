import Dubon2026.RationalTwoCyclicSubfieldConstructedNaturalAction
import Dubon2026.RationalPrimeCyclotomicReciprocityQuotientAction

/-! # Natural-unit action in one fixed two-power cyclotomic stage

The native normality theorem identifies the closure fields constructed for
different natural units. A primitive root generates every root of the same
order, so its power action transports without requiring the full cyclotomic
Galois group to be cyclic. This supplies the same-stage numerator and
denominator inputs to DUB-17's conductor-two principal-product calculation.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- A power action on a primitive root determines the same action on every
root of that order. No cyclicity of the automorphism group is needed. -/
theorem algEquiv_power_action_on_roots
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (m b : ℕ) (hm : m ≠ 0) (ζ : L) (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(L/K)) (hσ : σ ζ = ζ ^ b)
    (η : L) (hη : η ^ m = 1) : σ η = η ^ b := by
  letI : NeZero m := ⟨hm⟩
  obtain ⟨j, _, hj⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [← hj, map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm b j]

/-- Rewriting equal finite stages transports a primitive-root action to
any chosen root of the same order in the target stage. -/
theorem finiteGaloisStageAutCast_power_action
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {F G : FiniteGaloisIntermediateField K Ω} (h : F = G)
    (m b : ℕ) (hm : m ≠ 0) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (σ : Gal(F/K)) (hσ : σ ζ = ζ ^ b)
    (η : G) (hη : η ^ m = 1) :
    finiteGaloisStageAutCast h σ η = η ^ b := by
  subst G
  exact algEquiv_power_action_on_roots m b hm ζ hζ σ hσ η hη

/-- Casting the containing field preserves its literal restriction to a
fixed Galois subfield. The two inclusions are proof-irrelevantly identical. -/
theorem finiteGaloisStageAutCast_embeddedRestriction
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {F G : FiniteGaloisIntermediateField K Ω} (h : F = G)
    (L : FiniteGaloisIntermediateField K Ω)
    (hLF : L.toIntermediateField ≤ F.toIntermediateField)
    (hLG : L.toIntermediateField ≤ G.toIntermediateField)
    (σ : Gal(F/K)) :
    embeddedNormalGaloisRestriction (F := K) (IntermediateField.inclusion hLG)
        (finiteGaloisStageAutCast h σ) =
      embeddedNormalGaloisRestriction (F := K) (IntermediateField.inclusion hLF) σ := by
  subst G
  rfl

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]

include hn

/-- Every natural unit has its inverse-power reciprocity action on the
fixed cyclic subfield. The natural valuation-ring unit and all auxiliary
local structures are constructed, and the containing field stays fixed. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_fixed_natural_action
    (a : ℕ) (ha : ¬2 ∣ a) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n c v hv hc
    ∃ b : ℕ, b.Coprime (2 ^ (n + 1)) ∧ a * b ≡ 1 [MOD 2 ^ (n + 1)] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeNaturalUnit 2 Nat.prime_two a ha))).toMul =
          embeddedNormalGaloisRestriction (F := K) i σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  obtain ⟨u, hu, _⟩ := rationalPrimeNaturalWittIntertwiner_exists 2 Nat.prime_two a ha
  let Fa := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n a u hu ha
  have hF : Fa = F :=
    rationalPrimeOriginalCyclotomicClosureStage_eq 2 Nat.prime_two n a c u hu ha v hv hc
  have hLa : L.toIntermediateField ≤ Fa.toIntermediateField := by
    rw [hF]
    exact hL
  obtain ⟨b, hb, hab, σ, hσ, hrec⟩ :=
    rationalTwoOriginalCyclotomicClosure_cyclicSubfield_constructed_natural_action
      n a hn u hu ha L hLa
  refine ⟨b, hb, hab, finiteGaloisStageAutCast hF σ, ?_, ?_⟩
  · exact finiteGaloisStageAutCast_power_action hF (2 ^ (n + 1)) b (pow_ne_zero _ (by decide))
      (rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n a u hu ha)
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n a u hu ha)
      σ hσ _
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n c v hv hc).pow_eq_one
  · exact hrec.trans (finiteGaloisStageAutCast_embeddedRestriction hF L hLa hL σ).symm

end
end Dubon2026
