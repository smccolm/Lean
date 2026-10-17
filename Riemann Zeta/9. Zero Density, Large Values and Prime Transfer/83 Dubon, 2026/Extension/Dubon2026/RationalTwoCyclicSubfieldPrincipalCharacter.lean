import Dubon2026.RationalTwoCyclicSubfieldOrderZeroCharacter
import Dubon2026.RationalTwoCyclicSubfieldNormalizedResidual
import Dubon2026.RationalTwoSignedResidualReduction

/-! # The conductor-two principal character on the original cyclic subfield

The original reciprocity value of any rational unit is the restriction of
an actual containing-field automorphism. Its character cancels the real sign
and the finite away-prime product of the same normalized rational residual.
This is the local character conclusion needed for DUB-17's global arithmetic
completion comparison; it does not assert that comparison or invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators ValuativeRel

variable
    (n c : ℕ) (hn : 1 ≤ n)
    (v : 𝒪[rationalPrimeLocalField 2 Nat.prime_two]ˣ) (hv : v.val = c) (hc : ¬2 ∣ c)
    (L : FiniteGaloisIntermediateField (rationalPrimeLocalField 2 Nat.prime_two)
      (rationalPrimeLocalClosure 2 Nat.prime_two))
    (hL : L.toIntermediateField ≤
      (rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc).toIntermediateField)
    [IsCyclic Gal(L/rationalPrimeLocalField 2 Nat.prime_two)]
    (q : ℚˣ)

include hn

/-- The inverse-residue character describes the original reciprocity of an
arbitrary rational unit after its exact normalized two-power is removed. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_rational_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    let hr := rationalPrimeNormalizedResidual_order 2 Nat.prime_two q
    ∃ σ : Gal(F/K),
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive 2 Nat.prime_two n c v hv hc).autToPow K σ *
        rationalPrimeOrderZeroReduction 2 Nat.prime_two (n + 1)
          (rationalPrimeOrderZeroRationalUnit 2 Nat.prime_two r hr) = 1 ∧
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two q))).toMul =
          embeddedNormalGaloisRestriction (F := K) i σ := by
  obtain ⟨σ, hchar, hrec⟩ :=
    rationalTwoOriginalCyclotomicClosure_cyclicSubfield_orderZero_character
      n c hn v hv hc L hL (rationalPrimeNormalizedResidual 2 Nat.prime_two q)
      (rationalPrimeNormalizedResidual_order 2 Nat.prime_two q)
  refine ⟨σ, hchar, ?_⟩
  have heq := rationalTwoOriginalCyclotomicClosure_cyclicSubfield_reciprocity_normalizedResidual
    n c hn v hv hc L hL q
  exact (congrArg Additive.toMul heq.symm).trans hrec

/-- The real sign and finite away-prime product of the normalized residual
cancel the character of an actual containing-field automorphism restricting
to the original reciprocity value of the arbitrary rational unit. -/
theorem rationalTwoOriginalCyclotomicClosure_cyclicSubfield_principal_character :
    let K := rationalPrimeLocalField 2 Nat.prime_two
    let Ω := rationalPrimeLocalClosure 2 Nat.prime_two
    let F := rationalPrimeOriginalCyclotomicClosureStage 2 Nat.prime_two n c v hv hc
    let i : L →ₐ[K] F := IntermediateField.inclusion hL
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1),
        (∀ w ∉ S, w.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ w ∈ S, (Rat.HeightOneSpectrum.natGenerator w : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator w)
                (Rat.HeightOneSpectrum.prime_natGenerator w))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator w)
                  (Rat.HeightOneSpectrum.prime_natGenerator w) r))) = r.val ∧
        ∃ σ : Gal(F/K),
          (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
            2 Nat.prime_two n c v hv hc).autToPow K σ *
            arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r = 1 ∧
          (localFieldFiniteCyclicReciprocity K Ω L
            (Additive.ofMul (rationalPrimeRationalUnit 2 Nat.prime_two q))).toMul =
            embeddedNormalGaloisRestriction (F := K) i σ := by
  obtain ⟨S, hS, houtside, hproduct, hred⟩ :=
    rationalTwoNormalizedResidual_exists_signedReduction n q
  obtain ⟨σ, hchar, hrec⟩ :=
    rationalTwoOriginalCyclotomicClosure_cyclicSubfield_rational_character n c hn v hv hc L hL q
  refine ⟨S, hS, houtside, hproduct, σ, ?_, hrec⟩
  rw [← hred]
  exact hchar

end
end Dubon2026
