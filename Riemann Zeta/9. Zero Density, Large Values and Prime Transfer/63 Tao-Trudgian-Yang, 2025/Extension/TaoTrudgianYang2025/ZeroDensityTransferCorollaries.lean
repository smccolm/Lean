import TaoTrudgianYang2025.ZeroEndpointTwoBoundedRanges
import TaoTrudgianYang2025.LargeValueSubdivisionBounds
import TaoTrudgianYang2025.ClassicalDensityBridge

/-!
# The source two-thirds-range density corollaries

Powers two and three cover the printed compact general-LV interval. The
special coefficient 3-3*sigma then yields A(sigma) ≤ 3/tau0. Subdivision
proves the Montgomery-input variant; in the short-cutoff case the already
proved Ingham estimate supplies a stronger bound.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem isLargeValueBound_on_doubled_range_of_two_thirds_range
    {σ B τ₀ : ℝ} (hσ : 1/2 ≤ σ) (hσUpper : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hGeneral : ∀ τ ∈ Set.Icc (2*τ₀/3) τ₀, IsLargeValueBound σ τ (B*τ)) :
    ∀ τ ∈ Set.Icc (4*τ₀/3) (8*τ₀/3), IsLargeValueBound σ τ (B*τ) := by
  intro τ hτ
  have hτNonneg : 0 ≤ τ := by linarith [hτ.1]
  by_cases hTwo : τ ≤ 2*τ₀
  · have hMem : τ/2 ∈ Set.Icc (2*τ₀/3) τ₀ := by
      constructor <;> linarith [hτ.1]
    have hp := IsLargeValueBound.of_powered hσ hσUpper hτNonneg 2 (by omega)
      (hGeneral (τ/2) hMem)
    convert hp using 1
    norm_num
    ring
  · have hMem : τ/3 ∈ Set.Icc (2*τ₀/3) τ₀ := by
      constructor <;> linarith [hτ.2]
    have hp := IsLargeValueBound.of_powered hσ hσUpper hτNonneg 3 (by omega)
      (hGeneral (τ/3) hMem)
    convert hp using 1
    norm_num
    ring

theorem isZeroDensityBound_of_two_thirds_largeValue_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) (4*τ₀/3), IsZetaLargeValueBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc (2*τ₀/3) τ₀, IsLargeValueBound σ τ (B*τ)) :
    IsZeroDensityBound σ (B/(1-σ)) := by
  apply isZeroDensityBound_of_endpointTwo_bounded_largeValue_ranges
    σ B (4*τ₀/3) hσ hσUpper hB (by positivity) hZeta
  intro τ hτ
  apply isLargeValueBound_on_doubled_range_of_two_thirds_range hσ.le hσUpper.le hτ₀ hGeneral τ
  exact ⟨hτ.1,by linarith [hτ.2]⟩

theorem zeroDensityExponent_le_of_two_thirds_largeValue_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) (4*τ₀/3),
      zetaLargeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal))
    (hGeneral : ∀ τ ∈ Set.Icc (2*τ₀/3) τ₀,
      largeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal)) :
    zeroDensityExponent σ ≤ ((B/(1-σ) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound
    (isZeroDensityBound_of_two_thirds_largeValue_ranges σ B τ₀ hσ hσUpper hB hτ₀
      (fun τ hτ => isZetaLargeValueBound_of_exponent_le (hZeta τ hτ))
      (fun τ hτ => isLargeValueBound_of_exponent_le (hGeneral τ hτ)))

/-- Printed zero-large-cor2. -/
theorem zeroDensityExponent_le_three_div_of_largeValue_bounds
    (σ τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) (4*τ₀/3),
      zetaLargeValueExponent σ τ ≤ (((3-3*σ)*τ/τ₀ : ℝ) : EReal))
    (hGeneral : ∀ τ ∈ Set.Icc (2*τ₀/3) τ₀,
      largeValueExponent σ τ ≤ (((3-3*σ)*τ/τ₀ : ℝ) : EReal)) :
    zeroDensityExponent σ ≤ ((3/τ₀ : ℝ) : EReal) := by
  have hB : 0 ≤ (3-3*σ)/τ₀ := div_nonneg (by linarith) hτ₀.le
  have hz : ∀ τ ∈ Set.Ico (2 : ℝ) (4*τ₀/3),
      zetaLargeValueExponent σ τ ≤ ((((3-3*σ)/τ₀)*τ : ℝ) : EReal) := by
    simpa only [div_mul_eq_mul_div] using hZeta
  have hg : ∀ τ ∈ Set.Icc (2*τ₀/3) τ₀,
      largeValueExponent σ τ ≤ ((((3-3*σ)/τ₀)*τ : ℝ) : EReal) := by
    simpa only [div_mul_eq_mul_div] using hGeneral
  have h := zeroDensityExponent_le_of_two_thirds_largeValue_ranges
    σ ((3-3*σ)/τ₀) τ₀ hσ hσUpper hB hτ₀ hz hg
  have hEq : ((3-3*σ)/τ₀)/(1-σ) = 3/τ₀ := by
    have hGap : 1-σ ≠ 0 := by linarith
    field_simp
  simpa only [hEq] using h

/-- Printed zero-large-cor3, preserving its full positive-cutoff domain. -/
theorem zeroDensityExponent_le_three_div_of_montgomery_range
    (σ τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) (4*τ₀/3),
      zetaLargeValueExponent σ τ ≤ (((3-3*σ)*τ/τ₀ : ℝ) : EReal))
    (hMontgomery : ∀ τ ∈ Set.Icc (0 : ℝ) (τ₀+σ-1),
      largeValueExponent σ τ ≤ ((2-2*σ : ℝ) : EReal)) :
    zeroDensityExponent σ ≤ ((3/τ₀ : ℝ) : EReal) := by
  by_cases hCut : τ₀ < 3-3*σ
  · have hDen : τ₀ ≤ 2-σ := by linarith
    exact (zeroDensityExponent_le_ingham hσ hσUpper.le).trans
      (EReal.coe_le_coe_iff.mpr (div_le_div_of_nonneg_left (by norm_num) hτ₀ hDen))
  · have hCutLower : 3-3*σ ≤ τ₀ := le_of_not_gt hCut
    apply zeroDensityExponent_le_three_div_of_largeValue_bounds σ τ₀ hσ hσUpper hτ₀ hZeta
    intro τ hτ
    have hτPos : 0 ≤ τ := by linarith [hτ.1]
    have hFirst : 2-2*σ ≤ (3-3*σ)*τ/τ₀ := by
      apply (le_div_iff₀ hτ₀).mpr
      nlinarith [mul_nonneg (show 0 ≤ 3-3*σ by linarith)
        (show 0 ≤ τ-2*τ₀/3 by linarith [hτ.1])]
    by_cases hSmall : τ ≤ τ₀+σ-1
    · exact (hMontgomery τ ⟨hτPos,hSmall⟩).trans (EReal.coe_le_coe_iff.mpr hFirst)
    · have hBase : 0 ≤ τ₀+σ-1 := by linarith
      have hSub := (largeValueExponent_subdivision hσ.le hσUpper.le hBase
        (lt_of_not_ge hSmall).le).2
      have hValue := hMontgomery (τ₀+σ-1) ⟨hBase,le_rfl⟩
      have hSecond : (2-2*σ)+(τ-(τ₀+σ-1)) ≤ (3-3*σ)*τ/τ₀ := by
        apply (le_div_iff₀ hτ₀).mpr
        nlinarith [mul_nonneg (show 0 ≤ τ₀-(3-3*σ) by linarith)
          (show 0 ≤ τ₀-τ by linarith [hτ.2])]
      calc
        largeValueExponent σ τ ≤
            largeValueExponent σ (τ₀+σ-1)+((τ-(τ₀+σ-1) : ℝ) : EReal) := hSub
        _ ≤ ((2-2*σ : ℝ) : EReal)+((τ-(τ₀+σ-1) : ℝ) : EReal) :=
          add_le_add hValue le_rfl
        _ = (((2-2*σ)+(τ-(τ₀+σ-1)) : ℝ) : EReal) := (EReal.coe_add _ _).symm
        _ ≤ (((3-3*σ)*τ/τ₀ : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hSecond

/-- Printed zero-large-cor, with the exact two-thirds-range supremum. -/
theorem zeroDensityExponent_le_two_thirds_suprema
    (σ τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1) (hτ₀ : 0 < τ₀) :
    zeroDensityExponent σ*((1-σ : ℝ) : EReal) ≤
      max (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ/(τ : EReal)) '' Set.Ico 2 (4*τ₀/3)))
        (sSup ((fun τ : ℝ => largeValueExponent σ τ/(τ : EReal)) '' Set.Icc (2*τ₀/3) τ₀)) := by
  let R : EReal := max
    (sSup ((fun τ : ℝ => zetaLargeValueExponent σ τ/(τ : EReal)) '' Set.Ico 2 (4*τ₀/3)))
    (sSup ((fun τ : ℝ => largeValueExponent σ τ/(τ : EReal)) '' Set.Icc (2*τ₀/3) τ₀))
  have hR : 0 ≤ R := by
    have hNonneg : (0 : EReal) ≤ largeValueExponent σ τ₀/(τ₀ : EReal) :=
      EReal.div_nonneg (largeValueExponent_nonneg hσ.le hσUpper.le hτ₀.le)
        (EReal.coe_nonneg.mpr hτ₀.le)
    have hMem : largeValueExponent σ τ₀/(τ₀ : EReal) ≤
        sSup ((fun τ : ℝ => largeValueExponent σ τ/(τ : EReal)) '' Set.Icc (2*τ₀/3) τ₀) :=
      le_sSup ⟨τ₀,⟨by linarith,le_rfl⟩,rfl⟩
    exact hNonneg.trans (hMem.trans (le_max_right _ _))
  change zeroDensityExponent σ*((1-σ : ℝ) : EReal) ≤ R
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hRB
  have hB : 0 ≤ B := EReal.coe_nonneg.mp (hR.trans hRB.le)
  have hZeta : ∀ τ ∈ Set.Ico (2 : ℝ) (4*τ₀/3),
      zetaLargeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal) := by
    intro τ hτ
    have hτPos : 0 < τ := by linarith [hτ.1]
    have hSup : zetaLargeValueExponent σ τ/(τ : EReal) ≤
        sSup ((fun t : ℝ => zetaLargeValueExponent σ t/(t : EReal)) '' Set.Ico 2 (4*τ₀/3)) :=
      le_sSup ⟨τ,hτ,rfl⟩
    have hRatio := hSup.trans ((le_max_left _ _).trans hRB.le)
    have hMul := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτPos) (EReal.coe_ne_top τ)).mp hRatio
    simpa only [← EReal.coe_mul,mul_comm τ B] using hMul
  have hGeneral : ∀ τ ∈ Set.Icc (2*τ₀/3) τ₀,
      largeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal) := by
    intro τ hτ
    have hτPos : 0 < τ := by linarith [hτ.1]
    have hSup : largeValueExponent σ τ/(τ : EReal) ≤
        sSup ((fun t : ℝ => largeValueExponent σ t/(t : EReal)) '' Set.Icc (2*τ₀/3) τ₀) :=
      le_sSup ⟨τ,hτ,rfl⟩
    have hRatio := hSup.trans ((le_max_right _ _).trans hRB.le)
    have hMul := (EReal.div_le_iff_le_mul (EReal.coe_pos.mpr hτPos) (EReal.coe_ne_top τ)).mp hRatio
    simpa only [← EReal.coe_mul,mul_comm τ B] using hMul
  have hZero := zeroDensityExponent_le_of_two_thirds_largeValue_ranges
    σ B τ₀ hσ hσUpper hB hτ₀ hZeta hGeneral
  apply (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr (by linarith : 0 < 1-σ))
    (EReal.coe_ne_top (1-σ))).mp
  simpa only [← EReal.coe_div] using hZero

end TaoTrudgianYang2025
