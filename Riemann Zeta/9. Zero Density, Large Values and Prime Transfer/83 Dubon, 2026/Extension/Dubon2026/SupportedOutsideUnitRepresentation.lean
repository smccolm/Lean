import Dubon2026.NumberFieldIntegerUnitTransports
import Dubon2026.SUnitLogPlaceAction

/-! # Original integer-unit factors outside a stable support

The complement carries its actual original prime action. Its original
integer-unit transports form the coefficient representation to which
unramified local vanishing and cyclic product vanishing must be applied
in DUB-17's supported-idele Herbrand calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual prime permutation restricted to the complement of the stable support. -/
@[reducible]
def supportedOutsidePlaceAction :
    MulAction Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} where
  smul σ v := ⟨numberFieldGaloisPlaceEquiv K L σ v.val,
    fun hv => v.property ((hS σ v.val).mpr hv)⟩
  one_smul v := Subtype.ext (numberFieldGaloisPlaceEquiv_one K L v.val)
  mul_smul σ τ v := Subtype.ext (numberFieldGaloisPlaceEquiv_mul K L σ τ v.val)

/-- The original integer-unit transport on actual outside-support places. -/
def supportedOutsideUnitTransport :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (v w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}), σ • v = w →
      Additive (v.val.adicCompletionIntegers L)ˣ ≃ₗ[ℤ]
        Additive (w.val.adicCompletionIntegers L)ˣ := by
  intro σ v w h
  exact numberFieldIntegerUnitTransport K L σ v.val w.val (congrArg Subtype.val h)

/-- The actual outside-support transport satisfies the identity law. -/
theorem supportedOutsideUnitTransport_one :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ (v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
      (x : Additive (v.val.adicCompletionIntegers L)ˣ),
      supportedOutsideUnitTransport K L S hS 1 v v (one_smul Gal(L/K) v) x = x := by
  intro v x
  exact numberFieldIntegerUnitTransport_one K L v.val x

/-- The actual outside-support transport satisfies the original composition law. -/
theorem supportedOutsideUnitTransport_mul :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (v u w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
      (hτ : τ • v = u) (hσ : σ • u = w) (hστ : (σ * τ) • v = w)
      (x : Additive (v.val.adicCompletionIntegers L)ˣ),
      supportedOutsideUnitTransport K L S hS (σ * τ) v w hστ x =
        supportedOutsideUnitTransport K L S hS σ u w hσ
          (supportedOutsideUnitTransport K L S hS τ v u hτ x) := by
  intro σ τ v u w hτ hσ hστ x
  exact numberFieldIntegerUnitTransport_mul K L σ τ v.val u.val w.val
    (congrArg Subtype.val hτ) (congrArg Subtype.val hσ) (congrArg Subtype.val hστ) x

/-- The actual outside-support original integer-unit product with its original Galois action. -/
def supportedOutsideUnitRep : Rep ℤ Gal(L/K) := by
  letI := supportedOutsidePlaceAction K L S hS
  exact transportedPiRep ℤ Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS)

end
end Dubon2026
