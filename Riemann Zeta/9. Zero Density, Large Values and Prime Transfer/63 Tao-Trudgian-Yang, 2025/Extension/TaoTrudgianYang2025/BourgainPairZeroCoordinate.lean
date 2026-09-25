import TaoTrudgianYang2025.BourgainPairLongCutoff

/-! The zero first-coordinate case requires no division by the pair parameter. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem ExponentPair.zero_first_coordinate_density {l σ : ℝ}
    (hpair : ExponentPair 0 l) (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (hline : (l+1)/2 < σ) :
    zeroDensityExponent σ ≤ (0 : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro B hB
  have hBp : 0 < B := by
    change ((0 : ℝ) : EReal) < (B : EReal) at hB
    exact EReal.coe_lt_coe_iff.mp hB
  have h := zeroDensityExponent_le_three_div_of_montgomery_range
    σ (3/B) hσ hσ1 (div_pos (by norm_num) hBp)
  have hz : ∀ τ ∈ Set.Ico (2 : ℝ) (4*(3/B)/3),
      zetaLargeValueExponent σ τ ≤ (((3-3*σ)*τ/(3/B) : ℝ) : EReal) := by
    intro τ hτ
    have hn := hpair.aProcess.zetaLargeValueExponent_eq_bot_of_one_le_tau
      hσ.le (show 1 ≤ τ by linarith [hτ.1])
      (by norm_num; linarith : 0/(2*0+2)*τ+(l/(2*0+2)+1/2)-0/(2*0+2) < σ)
    rw [hn]
    exact bot_le
  have hm : ∀ τ ∈ Set.Icc (0 : ℝ) (3/B+σ-1),
      largeValueExponent σ τ ≤ ((2-2*σ : ℝ) : EReal) := by
    intro τ hτ
    exact largeValueExponent_le_of_bound
      (hpair.local_largeValueBound hτ.1 (by linarith))
  have hout := h hz hm
  have he : 3/(3/B) = B := by field_simp
  simpa only [he] using hout

end TaoTrudgianYang2025
