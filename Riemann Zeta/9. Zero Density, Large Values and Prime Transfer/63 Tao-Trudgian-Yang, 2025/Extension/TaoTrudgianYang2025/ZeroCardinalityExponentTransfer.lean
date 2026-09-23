import TaoTrudgianYang2025.ZeroCardinalityTransfer
import TaoTrudgianYang2025.LargeValueNonnegative
import TaoTrudgianYang2025.LargeValueBoundClosure
import TaoTrudgianYang2025.ZetaLargeValueBoundClosure
import Mathlib.Data.EReal.Inv
import Mathlib.Order.LiminfLimsup

/-!
# Endpoint-one sup/limsup transfer of cardinality exponents

The envelope starts at zeta height one. This is an explicitly labeled
intermediate theorem, not a change to the printed endpoint-two contract.
-/

noncomputable section
namespace TaoTrudgianYang2025

def zeroCardinalityTransferEnvelope (σ : ℝ) : EReal :=
  max (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ / (τ : EReal)) '' Set.Ici 1))
    (Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop)

/-- The actual singleton lower bound makes the general limsup nonnegative. -/
theorem zeroCardinalityTransferEnvelope_nonneg (σ : ℝ)
    (hσLower : 1/2 ≤ σ) (hσ : σ ≤ 1) :
    0 ≤ zeroCardinalityTransferEnvelope σ := by
  have he : ∀ᶠ τ : ℝ in Filter.atTop,
      (0 : EReal) ≤ largeValueExponent σ τ / (τ : EReal) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact EReal.div_nonneg (largeValueExponent_nonneg hσLower hσ hτ)
      (EReal.coe_nonneg.mpr hτ)
  have hlim : (0 : EReal) ≤
      Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop := by
    simpa using Filter.limsup_le_limsup he
  exact hlim.trans (le_max_right _ _)

/-- Unconditional endpoint-one sup/limsup cardinality transfer.
It consumes the actual source Type-I/II construction and multiplicity-weighted
symmetric zero count. The printed endpoint-two strengthening is separate. -/
theorem zeroDensityExponent_le_sup_limsup_endpoint_one
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1) :
    zeroDensityExponent σ * ((1 - σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ / (τ : EReal)) '' Set.Ici 1))
        (Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop) := by
  change zeroDensityExponent σ * ((1 - σ : ℝ) : EReal) ≤ zeroCardinalityTransferEnvelope σ
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hEnvelope
  have hB : 0 < B := EReal.coe_pos.mp
    ((zeroCardinalityTransferEnvelope_nonneg σ hσ.le hσUpper.le).trans_lt hEnvelope)
  have hZeta : ∀ τ : ℝ, 1 ≤ τ → IsZetaLargeValueBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := zero_lt_one.trans_le hτ
    apply isZetaLargeValueBound_of_exponent_le
    have hsup : zetaLargeValueExponent σ τ / (τ : EReal) ≤
        sSup ((fun u : ℝ => zetaLargeValueExponent σ u / (u : EReal)) '' Set.Ici 1) :=
      le_sSup ⟨τ, hτ, rfl⟩
    have hratio : zetaLargeValueExponent σ τ / (τ : EReal) ≤
        zeroCardinalityTransferEnvelope σ := hsup.trans (le_max_left _ _)
    have hp := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτpos)
      (EReal.coe_ne_top τ)).mp (hratio.trans hEnvelope.le)
    simpa only [← EReal.coe_mul, mul_comm τ B] using hp
  have hlimsup :
      Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop <
        (B : EReal) := (le_max_right _ _).trans_lt hEnvelope
  obtain ⟨τ₁, hτ₁⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hlimsup)
  let τ₀ := max 1 τ₁
  have hτ₀ : 0 < τ₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := hτ₀.trans_le hτ
    apply isLargeValueBound_of_exponent_le
    have hratio := (hτ₁ τ ((le_max_right _ _).trans hτ)).le
    have hp := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτpos)
      (EReal.coe_ne_top τ)).mp hratio
    simpa only [← EReal.coe_mul, mul_comm τ B] using hp
  have hzero := zeroDensityExponent_le_of_bound
    (isZeroDensityBound_of_uniform_largeValue_bounds σ B τ₀ hσ hσUpper hB.le hτ₀ hZeta hGeneral)
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1 - σ))
    (EReal.coe_ne_top (1 - σ))).mp
  simpa only [← EReal.coe_div] using hzero


end TaoTrudgianYang2025
