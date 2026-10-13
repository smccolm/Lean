import Dubon2026.OriginalFinitePowerIndex

/-! # Exact original integer-unit power index away from the exponent

The already proved original field-unit index and uniformizer factor give
integer-unit index n away from the original primes dividing n. The original
integer-ring comparison transports the quotient literally. This is the
target cardinality needed to prove the selected S-unit local-power map
surjective in DUB-17's principal localization chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- Outside the original primes dividing the exponent, the original local
integer-unit power quotient has exactly n elements. -/
theorem originalAdicIntegerPowerQuotient_card_away
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ n) (hv : (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletionIntegers K)ˣ).range) = n := by
  let F := v.adicCompletion K
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
  haveI : ProperSpace F := original_adicCompletion_properSpace K v
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := normValuation_isNonarchimedeanLocalField F
  let O := (ValuativeRel.valuation F).integer
  let eu := Units.mapEquiv (originalAdicIntegerNormEquiv K v).toMulEquiv
  have hQ : Nat.card ((v.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom n).range) =
      Nat.card (Oˣ ⧸ (powMonoidHom n).range) :=
    Nat.card_congr (QuotientGroup.congr _ _ eu (eu.map_range_powMonoidHom n)).toEquiv
  have hNonzero : (Ideal.span {(n : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ :=
    Submodule.span_singleton_eq_bot.mp.mt (Nat.cast_ne_zero.mpr hn.ne')
  have hNotDvd : ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    intro h
    exact hv ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton _)))
  have hNorm : Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)})) = 1 := by
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hNonzero,
      multiplicity_eq_zero.mpr hNotDvd, pow_zero, map_one]
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * Nat.card ((v.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom n).range) =
        n * Nat.card (Oˣ ⧸ (powMonoidHom n).range) := congrArg (n * ·) hQ
    _ = Nat.card (Fˣ ⧸ (powMonoidHom n).range) :=
      (localField_unitPower_index_uniformizer_factor F n).symm
    _ = n * n := by
      rw [originalFinitePowerQuotient_card K v n hn ζ hζ, hNorm, mul_one]

end
end Dubon2026
