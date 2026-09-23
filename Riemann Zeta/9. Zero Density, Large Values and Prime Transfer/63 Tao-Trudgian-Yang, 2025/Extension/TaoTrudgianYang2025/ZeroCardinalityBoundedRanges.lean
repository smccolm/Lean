import TaoTrudgianYang2025.ZeroCardinalityExponentTransfer
import TaoTrudgianYang2025.LargeValuePowering

/-!
# Endpoint-one bounded-range cardinality-to-density corollaries

The general range is reduced by the corrected cardinality powering witness.
The short zeta interval still starts at one, not the printed endpoint two.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem isZeroDensityBound_of_bounded_largeValue_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (1 : ℝ) τ₀, IsZetaLargeValueBound σ τ (B*τ))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀), IsLargeValueBound σ τ (B*τ)) :
    IsZeroDensityBound σ (B/(1-σ)) := by
  have hg := isLargeValueBound_of_bounded_power_range hσ.le hσUpper.le hτ₀ hGeneral
  apply isZeroDensityBound_of_uniform_largeValue_bounds σ B τ₀ hσ hσUpper hB hτ₀ _ hg
  intro τ hτ
  by_cases ht : τ < τ₀
  · exact hZeta τ ⟨hτ, ht⟩
  · exact (hg τ (le_of_not_gt ht)).toZeta

theorem zeroDensityExponent_le_of_bounded_largeValue_ranges
    (σ B τ₀ : ℝ) (hσ : 1/2 < σ) (hσUpper : σ < 1)
    (hB : 0 ≤ B) (hτ₀ : 0 < τ₀)
    (hZeta : ∀ τ ∈ Set.Ico (1 : ℝ) τ₀,
      zetaLargeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal))
    (hGeneral : ∀ τ ∈ Set.Icc τ₀ (2*τ₀),
      largeValueExponent σ τ ≤ ((B*τ : ℝ) : EReal)) :
    zeroDensityExponent σ ≤ ((B/(1-σ) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound
    (isZeroDensityBound_of_bounded_largeValue_ranges σ B τ₀ hσ hσUpper hB hτ₀
      (fun τ hτ => isZetaLargeValueBound_of_exponent_le (hZeta τ hτ))
      (fun τ hτ => isLargeValueBound_of_exponent_le (hGeneral τ hτ)))

end TaoTrudgianYang2025
