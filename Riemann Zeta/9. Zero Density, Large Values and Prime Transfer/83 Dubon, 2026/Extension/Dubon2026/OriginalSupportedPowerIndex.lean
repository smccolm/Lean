import Dubon2026.OriginalSupportedPowerQuotient
import Dubon2026.OriginalFinitePowerIndexProduct
import Dubon2026.OriginalInfinitePowerIndexProduct

/-! # Exact original supported-idele power index

All actual local quotient cardinalities are now evaluated. The actual
supported-idele quotient therefore has order n raised to twice the number
of infinite and selected finite places. This discharges the middle-term
numerical input to DUB-17's prime-degree class norm-index upper bound.
The selected-prime localization of the principal S-unit kernel remains.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- The actual original supported-idele power/local-unit quotient has the
exact numerical source cardinality once S contains the primes dividing n. -/
theorem originalSupportedPowerLocalUnitQuotient_card_exact
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) =
      n ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) := by
  rw [originalSupportedPowerLocalUnitQuotient_card,
    originalFinitePowerQuotient_product K n hn ζ hζ S hS]
  calc
    _ = ((∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸
        (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
          n ^ Module.finrank ℚ K) * n ^ (2 * S.card) := by ac_rfl
    _ = n ^ (2 * Fintype.card (InfinitePlace K)) * n ^ (2 * S.card) := by
      rw [originalInfinitePowerQuotient_product_mul_degree K n hn ζ hζ]
    _ = _ := by rw [← pow_add, Nat.mul_add]

end
end Dubon2026
