import TaoTrudgianYang2025.ZeroEndpointTwoTransfer
import TaoTrudgianYang2025.ZeroCardinalityExponentTransfer

/-!
# Source endpoint-two sup/limsup transfers

The cardinality theorem is the printed zero-from-large conclusion.
The energy version strengthens the already proved endpoint-one source
inequality and supports the printed bounded-range energy corollary.
-/

noncomputable section
namespace TaoTrudgianYang2025

def zeroCardinalityEndpointTwoEnvelope (σ : ℝ) : EReal :=
  max (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ / (τ : EReal)) '' Set.Ici 2))
    (Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop)

/-- The actual singleton lower bound makes the general limsup nonnegative. -/
theorem zeroCardinalityEndpointTwoEnvelope_nonneg (σ : ℝ)
    (hσLower : 1/2 ≤ σ) (hσ : σ ≤ 1) :
    0 ≤ zeroCardinalityEndpointTwoEnvelope σ := by
  have he : ∀ᶠ τ : ℝ in Filter.atTop,
      (0 : EReal) ≤ largeValueExponent σ τ / (τ : EReal) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact EReal.div_nonneg (largeValueExponent_nonneg hσLower hσ hτ)
      (EReal.coe_nonneg.mpr hτ)
  have hlim : (0 : EReal) ≤
      Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop := by
    simpa using Filter.limsup_le_limsup he
  exact hlim.trans (le_max_right _ _)

/-- The printed endpoint-two cardinality sup/limsup theorem. -/
theorem zeroDensityExponent_le_sup_limsup_endpoint_two
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1) :
    zeroDensityExponent σ * ((1 - σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ / (τ : EReal)) '' Set.Ici 2))
        (Filter.limsup (fun τ : ℝ => largeValueExponent σ τ / (τ : EReal)) Filter.atTop) := by
  change zeroDensityExponent σ * ((1 - σ : ℝ) : EReal) ≤ zeroCardinalityEndpointTwoEnvelope σ
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hEnvelope
  have hB : 0 < B := EReal.coe_pos.mp
    ((zeroCardinalityEndpointTwoEnvelope_nonneg σ hσ.le hσUpper.le).trans_lt hEnvelope)
  have hZeta : ∀ τ : ℝ, 2 ≤ τ → IsZetaLargeValueBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := by linarith
    apply isZetaLargeValueBound_of_exponent_le
    have hsup : zetaLargeValueExponent σ τ / (τ : EReal) ≤
        sSup ((fun u : ℝ => zetaLargeValueExponent σ u / (u : EReal)) '' Set.Ici 2) :=
      le_sSup ⟨τ, hτ, rfl⟩
    have hratio : zetaLargeValueExponent σ τ / (τ : EReal) ≤
        zeroCardinalityEndpointTwoEnvelope σ := hsup.trans (le_max_left _ _)
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
    (isZeroDensityBound_of_endpointTwo_largeValue_bounds σ B τ₀ hσ hσUpper hB.le hτ₀ hZeta hGeneral)
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1 - σ))
    (EReal.coe_ne_top (1 - σ))).mp
  simpa only [← EReal.coe_div] using hzero



def zeroEnergyEndpointTwoEnvelope (σ : ℝ) : EReal :=
  max (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ / (τ : EReal)) '' Set.Ici 2))
    (Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop)

/-- The general-energy limsup makes the transfer envelope nonnegative. -/
theorem zeroEnergyEndpointTwoEnvelope_nonneg (σ : ℝ) (hσ : σ ≤ 1) :
    0 ≤ zeroEnergyEndpointTwoEnvelope σ := by
  have he : ∀ᶠ τ : ℝ in Filter.atTop,
      (0 : EReal) ≤ largeValueEnergyExponent σ τ / (τ : EReal) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact EReal.div_nonneg (largeValueEnergyExponent_nonneg σ τ hσ)
      (EReal.coe_nonneg.mpr hτ)
  have hlim : (0 : EReal) ≤
      Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop := by
    simpa using Filter.limsup_le_limsup he
  exact hlim.trans (le_max_right _ _)

/-- Endpoint-two strengthening of the source energy sup/limsup transfer. -/
theorem zeroDensityEnergyExponent_le_sup_limsup_endpoint_two
    (σ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1) :
    zeroDensityEnergyExponent σ * ((1 - σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ / (τ : EReal)) '' Set.Ici 2))
        (Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop) := by
  change zeroDensityEnergyExponent σ * ((1 - σ : ℝ) : EReal) ≤ zeroEnergyEndpointTwoEnvelope σ
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hEnvelope
  have hB : 0 < B := EReal.coe_pos.mp
    ((zeroEnergyEndpointTwoEnvelope_nonneg σ hσUpper.le).trans_lt hEnvelope)
  have hZeta : ∀ τ : ℝ, 2 ≤ τ → IsZetaLargeValueEnergyBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := by linarith
    apply isZetaLargeValueEnergyBound_of_exponent_le hσ.le hσUpper.le hτpos.le
    have hsup : zetaLargeValueEnergyExponent σ τ / (τ : EReal) ≤
        sSup ((fun u : ℝ => zetaLargeValueEnergyExponent σ u / (u : EReal)) '' Set.Ici 2) :=
      le_sSup ⟨τ, hτ, rfl⟩
    have hratio : zetaLargeValueEnergyExponent σ τ / (τ : EReal) ≤
        zeroEnergyEndpointTwoEnvelope σ := hsup.trans (le_max_left _ _)
    have hp := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτpos)
      (EReal.coe_ne_top τ)).mp (hratio.trans hEnvelope.le)
    simpa only [← EReal.coe_mul, mul_comm τ B] using hp
  have hlimsup :
      Filter.limsup (fun τ : ℝ => largeValueEnergyExponent σ τ / (τ : EReal)) Filter.atTop <
        (B : EReal) := (le_max_right _ _).trans_lt hEnvelope
  obtain ⟨τ₁, hτ₁⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hlimsup)
  let τ₀ := max 1 τ₁
  have hτ₀ : 0 < τ₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hGeneral : ∀ τ : ℝ, τ₀ ≤ τ → IsLargeValueEnergyBound σ τ (B * τ) := by
    intro τ hτ
    have hτpos : 0 < τ := hτ₀.trans_le hτ
    apply isLargeValueEnergyBound_of_exponent_le hσ.le hσUpper.le hτpos.le
    have hratio := (hτ₁ τ ((le_max_right _ _).trans hτ)).le
    have hp := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτpos)
      (EReal.coe_ne_top τ)).mp hratio
    simpa only [← EReal.coe_mul, mul_comm τ B] using hp
  have hzero := zeroDensityEnergyExponent_le_of_bound
    (isZeroDensityEnergyBound_of_endpointTwo_energy_bounds σ B τ₀ hσ hσUpper hB.le hτ₀ hZeta hGeneral)
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1 - σ))
    (EReal.coe_ne_top (1 - σ))).mp
  simpa only [← EReal.coe_div] using hzero


end TaoTrudgianYang2025
