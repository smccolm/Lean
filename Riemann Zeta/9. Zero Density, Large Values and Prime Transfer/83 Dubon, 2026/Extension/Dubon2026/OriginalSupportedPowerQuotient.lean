import Dubon2026.OriginalSupportedPowerClassMap

/-! # The original supported-idele power quotient is the actual local product

The proved original component kernel and surjectivity give the exact
quotient equivalence. Its cardinal is the product of the actual local
power-class cardinalities, with no unproved numerical value substituted.
This is the middle term for DUB-17's principal S-unit exact-sequence
calculation and selected-prime norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The actual original supported-idele quotient by the actual power/local-unit conditions. -/
abbrev OriginalSupportedPowerLocalUnitQuotient :=
  numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) ⧸
    originalSupportedPowerLocalUnitSubgroup K n S T

/-- The original supported-idele quotient is the product of its actual finite and infinite local power classes. -/
def originalSupportedPowerLocalUnitQuotientEquiv :
    OriginalSupportedPowerLocalUnitQuotient K n S T ≃* OriginalSupportedLocalPowerClasses K n S :=
  (QuotientGroup.quotientMulEquivOfEq (originalSupportedPowerClassMap_ker K n S T).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (originalSupportedPowerClassMap K n S T)
      (originalSupportedPowerClassMap_surjective K n S T))

/-- The quotient equivalence preserves the actual local power classes of every original supported idele. -/
theorem originalSupportedPowerLocalUnitQuotientEquiv_mk
    (a : numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) :
    originalSupportedPowerLocalUnitQuotientEquiv K n S T
      (QuotientGroup.mk' (originalSupportedPowerLocalUnitSubgroup K n S T) a) =
        originalSupportedPowerClassMap K n S T a := rfl

/-- The original supported-idele quotient cardinal is exactly the product of its actual local power indices. -/
theorem originalSupportedPowerLocalUnitQuotient_card :
    Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) =
      (∏ w : InfinitePlace K, Nat.card
        (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
      ∏ v : S, Nat.card ((v.val.adicCompletion K)ˣ ⧸
        (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range) := by
  rw [Nat.card_congr (originalSupportedPowerLocalUnitQuotientEquiv K n S T).toEquiv]
  exact (Nat.card_prod _ _).trans (congrArg₂ (· * ·) Nat.card_pi Nat.card_pi)

end
end Dubon2026
