import Dubon2026.OriginalAdicScalarIdealPower

/-! # Exact original finite-completion scalar quotient cardinality

The existing prime-power ideal cardinality theorem and the proved original
residue comparison evaluate the scalar quotient needed for DUB-17's local
power index. The result is the norm of the original prime factor of `(n)`.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The actual completion integer ring modulo a positive integer has the
cardinality of the corresponding original prime-ideal norm factor. -/
theorem originalAdic_natCast_quotient_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      (Ideal.span {(n : v.adicCompletionIntegers K)} : Ideal (v.adicCompletionIntegers K))) =
      Ideal.absNorm (v.maxPowDividing (Ideal.span {(n : 𝓞 K)})) := by
  rw [originalAdic_natCast_span_eq_maximalIdeal_pow K v n hn]
  let O := v.adicCompletionIntegers K
  let m := multiplicity v.asIdeal (Ideal.span {(n : 𝓞 K)})
  have hp : Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ m) =
      Nat.card (O ⧸ IsLocalRing.maximalIdeal O) ^ m :=
    cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O)
  rw [hp]
  have hres : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = Ideal.absNorm v.asIdeal :=
    Nat.card_congr (originalRingOfIntegersQuotientEquivAdicResidueField K v).symm.toEquiv
  rw [hres]
  have hI : (Ideal.span {(n : 𝓞 K)} : Ideal (𝓞 K)) ≠ ⊥ :=
    Submodule.span_singleton_eq_bot.mp.mt (Nat.cast_ne_zero.mpr hn)
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow]

end
end Dubon2026
