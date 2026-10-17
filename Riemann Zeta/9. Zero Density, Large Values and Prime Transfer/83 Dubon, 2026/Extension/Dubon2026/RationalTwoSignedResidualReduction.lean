import Dubon2026.RationalPrimeCyclotomicResidualReduction

/-! # Exact signed away-prime reduction at the two-power conductor

The native finite-support product and order-zero reduction theorems already
allow the prime two. Their composition identifies the real sign and all
away-prime factors with the exact conductor residue of the same normalized
rational unit. This serves DUB-17's conductor-two principal-product assembly.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped BigOperators ValuativeRel

/-- The normalized rational residual has a finite signed prime product
away from two, and that product has its exact conductor reduction. -/
theorem rationalTwoNormalizedResidual_exists_signedReduction (n : ℕ) (q : ℚˣ) :
    let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
    let hr := rationalPrimeNormalizedResidual_order 2 Nat.prime_two q
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
        rationalPrimeOrderZeroReduction 2 Nat.prime_two (n + 1)
            (rationalPrimeOrderZeroRationalUnit 2 Nat.prime_two r hr) =
          arithmeticCyclotomicSignedAwayProductUnit (2 ^ (n + 1)) S hS r := by
  let r := rationalPrimeNormalizedResidual 2 Nat.prime_two q
  have hr := rationalPrimeNormalizedResidual_order 2 Nat.prime_two q
  obtain ⟨S, hpS, houtside, hproduct⟩ :=
    rationalPrimeNormalizedResidual_exists_away_signed_prime_product 2 Nat.prime_two q
  let hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ 2 ^ (n + 1) :=
    finiteSupport_away_primePower 2 Nat.prime_two (n + 1) S hpS
  have hsigned :
      (rationalPrimeSignedProductOrderZero 2 Nat.prime_two S hpS r :
          (rationalPrimeLocalField 2 Nat.prime_two)ˣ) =
        rationalPrimeRationalUnit 2 Nat.prime_two r :=
    rationalPrimeSignedProductOrderZero_eq_rationalUnit 2 Nat.prime_two S hpS r hproduct
  have hsubgroup :
      rationalPrimeSignedProductOrderZero 2 Nat.prime_two S hpS r =
        rationalPrimeOrderZeroRationalUnit 2 Nat.prime_two r hr :=
    Subtype.ext hsigned
  refine ⟨S, hS, houtside, hproduct, ?_⟩
  have hred := rationalPrimeOrderZeroReduction_signedProduct
    2 Nat.prime_two (n + 1) S hpS hS r
  rw [hsubgroup] at hred
  exact hred

end
end Dubon2026
