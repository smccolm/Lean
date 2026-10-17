import Dubon2026.RationalTwoCyclicSubfieldFixedStageAction

/-! # Quotient reciprocity on the same two-primary cyclic subfield

The two constructed natural-unit actions live in the same containing field.
Their quotient therefore restricts to the literal quotient reciprocity value.
This removes the numerator/denominator compatibility obligation in DUB-17's
conductor-two principal-product route.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- Two genuine upper-field actions combine under the original lower-field
reciprocity map. The restriction homomorphism preserves their quotient. -/
theorem restricted_quotient_primitiveRoot_action
    {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (ρ : Additive Kˣ →+ Additive Gal(L/K)) (R : Gal(F/K) →* Gal(L/K))
    (m b d e : ℕ) (hm : m ≠ 0) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (u v : Kˣ) (σu σv : Gal(F/K))
    (hu : σu ζ = ζ ^ b) (hv : σv ζ = ζ ^ e)
    (hde : d * e ≡ 1 [MOD m])
    (hrecU : (ρ (Additive.ofMul u)).toMul = R σu)
    (hrecV : (ρ (Additive.ofMul v)).toMul = R σv) :
    ∃ σ : Gal(F/K), σ ζ = ζ ^ (b * d) ∧
      (ρ (Additive.ofMul (u / v))).toMul = R σ := by
  refine ⟨σu * σv⁻¹, ?_, ?_⟩
  · have hinv : σv⁻¹ ζ = ζ ^ d :=
      algEquiv_inv_primitiveRoot_action m d e hm ζ hζ σv hv
        (by simpa only [Nat.mul_comm] using hde)
    change σu (σv⁻¹ ζ) = ζ ^ (b * d)
    rw [hinv, map_pow, hu, ← pow_mul]
  · change (ρ (Additive.ofMul u - Additive.ofMul v)).toMul = R (σu * σv⁻¹)
    rw [map_sub]
    change (ρ (Additive.ofMul u)).toMul * (ρ (Additive.ofMul v)).toMul⁻¹ = R (σu * σv⁻¹)
    rw [hrecU, hrecV, map_mul, map_inv]

/-- The proved family of natural actions supplies both quotient factors. -/
private theorem quotientAction_of_naturalFamily
    {K L F : Type*} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    (ρ : Additive Kˣ →+ Additive Gal(L/K)) (R : Gal(F/K) →* Gal(L/K))
    (m : ℕ) (hm : m ≠ 0) (ζ : F) (hζ : IsPrimitiveRoot ζ m)
    (u : (a : ℕ) → ¬2 ∣ a → Kˣ)
    (h : ∀ a ha, ∃ b : ℕ, b.Coprime m ∧ a * b ≡ 1 [MOD m] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ b ∧ (ρ (Additive.ofMul (u a ha))).toMul = R σ)
    (a d : ℕ) (ha : ¬2 ∣ a) (hd : ¬2 ∣ d) :
    ∃ b e : ℕ, b.Coprime m ∧ e.Coprime m ∧
      a * b ≡ 1 [MOD m] ∧ d * e ≡ 1 [MOD m] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ (b * d) ∧
        (ρ (Additive.ofMul (u a ha / u d hd))).toMul = R σ := by
  obtain ⟨b, hb, hab, σa, hσa, hrecA⟩ := h a ha
  obtain ⟨e, he, hde, σd, hσd, hrecD⟩ := h d hd
  refine ⟨b, e, hb, he, hab, hde, ?_⟩
  exact restricted_quotient_primitiveRoot_action ρ R m b d e hm ζ hζ
    (u a ha) (u d hd) σa σd hσa hσd hde hrecA hrecD

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]
    (a d : ℕ) (ha : ¬2 ∣ a) (hd : ¬2 ∣ d)

include hn

/-- A natural quotient acts by its inverse quotient exponent on the fixed
cyclotomic root, through an actual automorphism restricting to the original
reciprocity value on the cyclic subfield. Both natural actions are derived. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_quotient_action :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n c v hv hc
    ∃ b e : ℕ, b.Coprime (2 ^ (n + 1)) ∧ e.Coprime (2 ^ (n + 1)) ∧
      a * b ≡ 1 [MOD 2 ^ (n + 1)] ∧ d * e ≡ 1 [MOD 2 ^ (n + 1)] ∧
      ∃ σ : Gal(F/K), σ ζ = ζ ^ (b * d) ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeNaturalQuotientUnit 2 Nat.prime_two a d ha hd))).toMul =
          embeddedNormalGaloisRestriction (F := K) i σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
  let i : L →ₐ[K] F := IntermediateField.inclusion hL
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ζ := rationalPrimeOriginalCyclotomicClosureRoot 2 Nat.prime_two n c v hv hc
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  let R := embeddedNormalGaloisRestriction (F := K) i
  exact quotientAction_of_naturalFamily ρ R (2 ^ (n + 1))
    (pow_ne_zero _ (by decide)) ζ
    (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n c v hv hc)
    (rationalPrimeNaturalUnit 2 Nat.prime_two)
    (rationalTwoOriginalCyclotomicClosure_cyclicSubfield_fixed_natural_action n c hn v hv hc L hL)
    a d ha hd

end
end Dubon2026
