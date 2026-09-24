import TaoTrudgianYang2025.ZetaGrowthNonnegative
import TaoTrudgianYang2025.ZetaPairNonexistence

/-! The exact height-one boundary, using the actual classical pair. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem zetaLargeValueExponent_heightOne_eq_bot {σ : ℝ} (hσ : 1/2 < σ) :
    zetaLargeValueExponent σ 1 = ⊥ := by
  apply exponentPair_half_half.zetaLargeValueExponent_eq_bot
    (by norm_num) (by norm_num; exact hσ) (by linarith)

theorem IsZetaGrowthBound.heightOne_exponent_eq_bot {c m σ : ℝ}
    (hGrowth : IsZetaGrowthBound c m) (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hgap : c+m < σ) : zetaLargeValueExponent σ 1 = ⊥ := by
  apply zetaLargeValueExponent_heightOne_eq_bot
  have hm := hGrowth.closedStrip_nonneg hc hc1
  linarith

theorem zetaHeightOne_exponent_eq_bot_of_mu {c σ : ℝ}
    (hc : 1/2 ≤ c) (hc1 : c ≤ 1)
    (hgap : (c : EReal)+zetaGrowthExponent c < (σ : EReal)) :
    zetaLargeValueExponent σ 1 = ⊥ := by
  apply zetaLargeValueExponent_heightOne_eq_bot
  have hnonneg := zetaGrowthExponent_closedStrip_nonneg hc hc1
  have hcle : (c : EReal) ≤ (c : EReal)+zetaGrowthExponent c := by
    simpa only [add_zero] using add_le_add (le_refl (c : EReal)) hnonneg
  have hcs : c < σ := EReal.coe_lt_coe_iff.mp (hcle.trans_lt hgap)
  exact hc.trans_lt hcs

end TaoTrudgianYang2025
