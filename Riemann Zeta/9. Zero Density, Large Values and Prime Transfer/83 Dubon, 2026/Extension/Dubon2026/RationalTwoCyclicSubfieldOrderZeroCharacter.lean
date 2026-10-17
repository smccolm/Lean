import Dubon2026.RationalTwoCyclicSubfieldQuotientAction
import Dubon2026.PrimitiveRootQuotientCharacter

/-! # Exact conductor character for rational order-zero units at two

The existing positive-quotient approximation preserves the exact conductor
residue and supplies an actual norm from the chosen cyclic subfield.
Its reciprocity value consequently agrees with the proved quotient action.
This discharges the local inverse-residue identity required before DUB-17's
real/away-prime product and arithmetic-completion comparisons.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- The native positive-quotient norm comparison preserves the exact
conductor residue and the original cyclic-subfield reciprocity value. -/
theorem rationalTwoCyclicSubfield_exists_reciprocity_quotient_reduction
    (k : ℕ)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]
    (r : ℚˣ)
    (hr : localFieldUnitOrder (rationalPrimeLocalField 2 Nat.prime_two)
      (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two r)) = 0) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let ρ := localFieldFiniteCyclicReciprocity K Ω L
    ∃ (a d : ℕ) (ha : ¬2 ∣ a) (hd : ¬2 ∣ d),
      ρ (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two r)) =
        ρ (Additive.ofMul (rationalPrimeNaturalQuotientUnit 2 Nat.prime_two a d ha hd)) ∧
      rationalPrimeOrderZeroReduction 2 Nat.prime_two k
          (rationalPrimeOrderZeroRationalUnit 2 Nat.prime_two r hr) =
        ZMod.unitOfCoprime a (Nat.prime_two.coprime_pow_of_not_dvd ha) *
          (ZMod.unitOfCoprime d (Nat.prime_two.coprime_pow_of_not_dvd hd))⁻¹ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  obtain ⟨a, d, ha, hd, w, hw, hred⟩ :=
    rationalPrime_exists_positive_quotient_norm_comparison_reduction 2 Nat.prime_two k L r hr
  refine ⟨a, d, ha, hd, ?_, hred⟩
  have hzero := (localFieldFiniteCyclicReciprocity_eq_zero_iff K Ω L
      (rationalPrimeRationalUnit 2 Nat.prime_two r /
        rationalPrimeNaturalQuotientUnit 2 Nat.prime_two a d ha hd)).mpr ⟨w, hw⟩
  change ρ (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two r) -
    Additive.ofMul (rationalPrimeNaturalQuotientUnit 2 Nat.prime_two a d ha hd)) = 0 at hzero
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]
    (r : ℚˣ)
    (hr : localFieldUnitOrder (rationalPrimeLocalField 2 Nat.prime_two)
      (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two r)) = 0)

include hn

/-- The constructed quotient action gives the exact inverse-residue
character before applying the original rational norm comparison. -/
private theorem twoPrimaryQuotient_character
    (a d : ℕ) (ha : ¬2 ∣ a) (hd : ¬2 ∣ d) :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    ∃ σ : Gal(F/K),
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n c v hv hc).autToPow K σ *
        (ZMod.unitOfCoprime a (Nat.prime_two.coprime_pow_of_not_dvd ha) *
          (ZMod.unitOfCoprime d (Nat.prime_two.coprime_pow_of_not_dvd hd))⁻¹) = 1 ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeNaturalQuotientUnit 2 Nat.prime_two a d ha hd))).toMul =
          embeddedNormalGaloisRestriction (F := K) i σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  obtain ⟨b, _, hb, _, hab, _, σ, hσ, hrec⟩ :=
    rationalTwoOriginalCyclotomicClosure_cyclicSubfield_quotient_action n c hn v hv hc L hL a d ha hd
  refine ⟨σ, ?_, hrec⟩
  exact primitiveRoot_autToPow_mul_quotient_eq_one K F (2 ^ (n + 1))
    (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n c v hv hc)
    σ a b d (Nat.prime_two.coprime_pow_of_not_dvd ha) hb
    (Nat.prime_two.coprime_pow_of_not_dvd hd) hab hσ

/-- The original cyclic-subfield reciprocity of any rational order-zero
unit is the restriction of an actual cyclotomic automorphism whose character
is the inverse of the exact conductor reduction of that same unit. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_orderZero_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    ∃ σ : Gal(F/K),
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n c v hv hc).autToPow K σ *
        rationalPrimeOrderZeroReduction 2 Nat.prime_two (n + 1)
          (rationalPrimeOrderZeroRationalUnit 2 Nat.prime_two r hr) = 1 ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two r))).toMul =
          embeddedNormalGaloisRestriction (F := K) i σ := by
  let K := rationalPrimeLocalField 2 Nat.prime_two
  let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  obtain ⟨a, d, ha, hd, heq, hred⟩ :=
    rationalTwoCyclicSubfield_exists_reciprocity_quotient_reduction (n + 1) L r hr
  obtain ⟨σ, hchar, hrec⟩ := twoPrimaryQuotient_character n c hn v hv hc L hL a d ha hd
  refine ⟨σ, ?_, (congrArg Additive.toMul heq).trans hrec⟩
  rw [hred]
  exact hchar

end
end Dubon2026
