import TaoTrudgianYang2025.ZeroEndpointTwoExponentTransfer
import TaoTrudgianYang2025.ZeroCardinalityBoundedRanges

/-!
# Exact bounded-range zero-density and energy corollaries

The short zeta interval is [2,tau0), including its empty cases. The general
range [tau0,2*tau0] is extended by the corrected cardinality or energy
powering witness. No fifth-coordinate scaling is asserted or consumed.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem isZeroDensityBound_of_endpointTwo_bounded_largeValue_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) τ₀, IsZetaLargeValueBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀), IsLargeValueBound σ τ (B*τ)) :
    IsZeroDensityBound σ (B/(1-σ)) := by
  have hg := isLargeValueBound_of_bounded_power_range hσ.le hσUpper.le hτ₀ hGeneral
  apply isZeroDensityBound_of_endpointTwo_largeValue_bounds σ B τ₀ hσ hσUpper hB hτ₀ _ hg
  intro τ hτ
  by_cases ht : τ < τ₀
  · exact hZeta τ ⟨hτ, ht⟩
  · exact (hg τ (le_of_not_gt ht)).toZeta

theorem zeroDensityExponent_le_of_endpointTwo_bounded_largeValue_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) τ₀,
      zetaLargeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀),
      largeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal)) :
    zeroDensityExponent σ ≤ ((B/(1-σ) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound
    (isZeroDensityBound_of_endpointTwo_bounded_largeValue_ranges σ B τ₀ hσ hσUpper hB hτ₀
      (fun τ hτ => isZetaLargeValueBound_of_exponent_le (hZeta τ hτ))
      (fun τ hτ => isLargeValueBound_of_exponent_le (hGeneral τ hτ)))


theorem isZeroDensityEnergyBound_of_endpointTwo_bounded_energy_ranges
    (σ B τ₀ : ℝ) (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) τ₀, IsZetaLargeValueEnergyBound σ τ (B * τ))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2 * τ₀), IsLargeValueEnergyBound σ τ (B * τ)) :
    IsZeroDensityEnergyBound σ (B / (1 - σ)) := by
  have hg := isLargeValueEnergyBound_of_bounded_power_range hσ.le hσUpper.le hτ₀ hGeneral
  apply isZeroDensityEnergyBound_of_endpointTwo_energy_bounds σ B τ₀ hσ hσUpper hB hτ₀ _ hg
  intro τ hτ
  by_cases ht : τ < τ₀
  · exact hZeta τ ⟨hτ, ht⟩
  · exact (hg τ (le_of_not_gt ht)).toZeta


theorem zeroDensityEnergyExponent_le_of_endpointTwo_bounded_energy_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) τ₀,
      zetaLargeValueEnergyExponent σ τ ≤ ((B*τ : ℝ) : EReal))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀),
      largeValueEnergyExponent σ τ ≤ ((B*τ : ℝ) : EReal)) :
    zeroDensityEnergyExponent σ ≤ ((B/(1-σ) : ℝ) : EReal) :=
  zeroDensityEnergyExponent_le_of_bound
    (isZeroDensityEnergyBound_of_endpointTwo_bounded_energy_ranges σ B τ₀ hσ hσUpper hB hτ₀
      (fun τ hτ => isZetaLargeValueEnergyBound_of_exponent_le hσ.le hσUpper.le
        (by linarith [hτ.1]) (hZeta τ hτ))
      (fun τ hτ => isLargeValueEnergyBound_of_exponent_le hσ.le hσUpper.le
        (hτ₀.le.trans hτ.1) (hGeneral τ hτ)))

/-- Printed zero-large-cor-0, with the exact half-open/closed intervals. -/
theorem zeroDensityExponent_le_endpointTwo_bounded_suprema
    (σ τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1) (hτ₀ : 0 < τ₀) :
    zeroDensityExponent σ*((1-σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ/(τ : EReal)) '' Set.Ico 2 τ₀))
        (sSup ((fun τ : ℝ => largeValueExponent σ τ/(τ : EReal)) '' Set.Icc τ₀ (2*τ₀))) := by
  let R : EReal := max
    (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ/(τ : EReal)) '' Set.Ico 2 τ₀))
    (sSup ((fun τ : ℝ => largeValueExponent σ τ/(τ : EReal)) '' Set.Icc τ₀ (2*τ₀)))
  have hR : 0 ≤ R := by
    have hNonneg : (0 : EReal) ≤ largeValueExponent σ τ₀/(τ₀ : EReal) :=
      EReal.div_nonneg (largeValueExponent_nonneg hσ.le hσUpper.le hτ₀.le)
        (EReal.coe_nonneg.mpr hτ₀.le)
    have hMem : largeValueExponent σ τ₀/(τ₀ : EReal) ≤
        sSup ((fun τ : ℝ => largeValueExponent σ τ/(τ : EReal)) '' Set.Icc τ₀ (2*τ₀)) :=
      le_sSup ⟨τ₀,⟨le_rfl,by linarith⟩,rfl⟩
    exact hNonneg.trans (hMem.trans (le_max_right _ _))
  change zeroDensityExponent σ*((1-σ : ℝ) : EReal) ≤ R
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hRB
  have hB : 0 ≤ B := EReal.coe_nonneg.mp (hR.trans hRB.le)
  have hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) τ₀,
      zetaLargeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal) := by
    intro τ hτ
    have hτPos : 0 < τ := by linarith [hτ.1]
    have hSup : zetaLargeValueExponent σ τ/(τ : EReal) ≤
        sSup ((fun t : ℝ => zetaLargeValueExponent σ t/(t : EReal)) '' Set.Ico 2 τ₀) :=
      le_sSup ⟨τ,hτ,rfl⟩
    have hRatio := hSup.trans ((le_max_left _ _).trans hRB.le)
    have hMul := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτPos) (EReal.coe_ne_top τ)).mp hRatio
    simpa only [← EReal.coe_mul,mul_comm τ B] using hMul
  have hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀),
      largeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal) := by
    intro τ hτ
    have hτPos : 0 < τ := hτ₀.trans_le hτ.1
    have hSup : largeValueExponent σ τ/(τ : EReal) ≤
        sSup ((fun t : ℝ => largeValueExponent σ t/(t : EReal)) '' Set.Icc τ₀ (2*τ₀)) :=
      le_sSup ⟨τ,hτ,rfl⟩
    have hRatio := hSup.trans ((le_max_right _ _).trans hRB.le)
    have hMul := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτPos) (EReal.coe_ne_top τ)).mp hRatio
    simpa only [← EReal.coe_mul,mul_comm τ B] using hMul
  have hZero := zeroDensityExponent_le_of_endpointTwo_bounded_largeValue_ranges
    σ B τ₀ hσ hσUpper hB hτ₀ hZeta hGeneral
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1-σ))
    (EReal.coe_ne_top (1-σ))).mp
  simpa only [← EReal.coe_div] using hZero

/-- Printed zeroe-large-cor-0, with the exact half-open/closed intervals. -/
theorem zeroDensityEnergyExponent_le_endpointTwo_bounded_suprema
    (σ τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1) (hτ₀ : 0 < τ₀) :
    zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ/(τ : EReal)) '' Set.Ico 2 τ₀))
        (sSup ((fun τ : ℝ => largeValueEnergyExponent σ τ/(τ : EReal)) '' Set.Icc τ₀ (2*τ₀))) := by
  let R : EReal := max
    (sSup ((fun τ : ℝ => zetaLargeValueEnergyExponent σ τ/(τ : EReal)) '' Set.Ico 2 τ₀))
    (sSup ((fun τ : ℝ => largeValueEnergyExponent σ τ/(τ : EReal)) '' Set.Icc τ₀ (2*τ₀)))
  have hR : 0 ≤ R := by
    have hNonneg : (0 : EReal) ≤ largeValueEnergyExponent σ τ₀/(τ₀ : EReal) :=
      EReal.div_nonneg (largeValueEnergyExponent_nonneg σ τ₀ hσUpper.le)
        (EReal.coe_nonneg.mpr hτ₀.le)
    have hMem : largeValueEnergyExponent σ τ₀/(τ₀ : EReal) ≤
        sSup ((fun τ : ℝ => largeValueEnergyExponent σ τ/(τ : EReal)) '' Set.Icc τ₀ (2*τ₀)) :=
      le_sSup ⟨τ₀,⟨le_rfl,by linarith⟩,rfl⟩
    exact hNonneg.trans (hMem.trans (le_max_right _ _))
  change zeroDensityEnergyExponent σ*((1-σ : ℝ) : EReal) ≤ R
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hRB
  have hB : 0 ≤ B := EReal.coe_nonneg.mp (hR.trans hRB.le)
  have hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) τ₀,
      zetaLargeValueEnergyExponent σ τ ≤ ((B*τ : ℝ) : EReal) := by
    intro τ hτ
    have hτPos : 0 < τ := by linarith [hτ.1]
    have hSup : zetaLargeValueEnergyExponent σ τ/(τ : EReal) ≤
        sSup ((fun t : ℝ => zetaLargeValueEnergyExponent σ t/(t : EReal)) '' Set.Ico 2 τ₀) :=
      le_sSup ⟨τ,hτ,rfl⟩
    have hRatio := hSup.trans ((le_max_left _ _).trans hRB.le)
    have hMul := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτPos) (EReal.coe_ne_top τ)).mp hRatio
    simpa only [← EReal.coe_mul,mul_comm τ B] using hMul
  have hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀),
      largeValueEnergyExponent σ τ ≤ ((B*τ : ℝ) : EReal) := by
    intro τ hτ
    have hτPos : 0 < τ := hτ₀.trans_le hτ.1
    have hSup : largeValueEnergyExponent σ τ/(τ : EReal) ≤
        sSup ((fun t : ℝ => largeValueEnergyExponent σ t/(t : EReal)) '' Set.Icc τ₀ (2*τ₀)) :=
      le_sSup ⟨τ,hτ,rfl⟩
    have hRatio := hSup.trans ((le_max_right _ _).trans hRB.le)
    have hMul := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτPos) (EReal.coe_ne_top τ)).mp hRatio
    simpa only [← EReal.coe_mul,mul_comm τ B] using hMul
  have hZero := zeroDensityEnergyExponent_le_of_endpointTwo_bounded_energy_ranges
    σ B τ₀ hσ hσUpper hB hτ₀ hZeta hGeneral
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1-σ))
    (EReal.coe_ne_top (1-σ))).mp
  simpa only [← EReal.coe_div] using hZero

theorem endpointTwo_short_zeta_supremum_eq_bot
    (f : ℝ → EReal) (τ₀ : ℝ) (hτ₀ : τ₀ ≤ 2) :
    sSup (f '' Set.Ico 2 τ₀) = ⊥ := by
  simp [Set.Ico_eq_empty_of_le hτ₀]

end TaoTrudgianYang2025
