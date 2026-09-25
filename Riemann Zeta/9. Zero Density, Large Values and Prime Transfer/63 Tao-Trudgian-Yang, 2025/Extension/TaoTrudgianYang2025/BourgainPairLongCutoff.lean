import TaoTrudgianYang2025.ExponentPairLargeValues
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaPairNonexistence

/-!
# The long-cutoff branch of Bourgain's pair-to-density argument

The A-transformed pair excludes the actual zeta patterns below the
detector cutoff. The original pair supplies the actual Montgomery
range through sharp Gram sums. The complementary short-cutoff
branch of the printed theorem is not asserted here.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem ExponentPair.aProcess_zeta_cutoff {k l σ τ t : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (hσ : 1/2 ≤ σ)
    (hτ : 1 ≤ τ) (ht : τ < t)
    (hscale : k*t = 2*(1+k)*σ-1-l) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply hpair.aProcess.zetaLargeValueExponent_eq_bot_of_one_le_tau hσ hτ
  have hd : 0 < 2*k+2 := by linarith
  have he : k/(2*k+2)*τ+(l/(2*k+2)+1/2)-k/(2*k+2) =
      (k*τ+l+1)/(2*k+2) := by field_simp; ring
  rw [he]
  apply (div_lt_iff₀ hd).mpr
  have hh := mul_lt_mul_of_pos_left ht hk
  nlinarith

theorem ExponentPair.bourgain_density_long_cutoff {k l σ t : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 0 < t)
    (hscale : k*t = 2*(1+k)*σ-1-l)
    (hlong : 12*σ-8 ≤ t) :
    zeroDensityExponent σ ≤ ((4/t : ℝ) : EReal) := by
  have h := zeroDensityExponent_le_three_div_of_montgomery_range
    σ (3*t/4) hσ hσ1 (by positivity)
  have hz : ∀ τ ∈ Set.Ico (2 : ℝ) (4*(3*t/4)/3),
      zetaLargeValueExponent σ τ ≤ (((3-3*σ)*τ/(3*t/4) : ℝ) : EReal) := by
    intro τ hτ
    rw [hpair.aProcess_zeta_cutoff hk hσ.le (by linarith [hτ.1])
      (by linarith [hτ.2]) hscale]
    exact bot_le
  have hm : ∀ τ ∈ Set.Icc (0 : ℝ) (3*t/4+σ-1),
      largeValueExponent σ τ ≤ ((2-2*σ : ℝ) : EReal) := by
    intro τ hτ
    let c := t+1-2*σ
    have htc : τ ≤ c := by dsimp [c]; linarith [hτ.2]
    by_cases hc : 0 < c
    · have hcs : k*c = 2*σ-1-l+k := by dsimp [c]; nlinarith
      exact largeValueExponent_le_of_bound
        ((hpair.closed_local_largeValueBound hk hc hcs).of_height_le htc)
    · have ht0 : τ = 0 := by linarith [hτ.1]
      have hb := largeValueExponent_le_tau σ hτ.1
      rw [ht0] at hb ⊢
      exact hb.trans (EReal.coe_le_coe_iff.mpr (show (0 : ℝ) ≤ 2-2*σ by linarith))
  have hout := h hz hm
  have he : 3/(3*t/4) = 4/t := by field_simp
  simpa only [he] using hout

theorem ExponentPair.bourgain_density_long_branch {k l σ : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (hd : 0 < 2*(1+k)*σ-1-l)
    (hlong : 12*σ-8 ≤ (2*(1+k)*σ-1-l)/k) :
    zeroDensityExponent σ ≤
      ((4*k/(2*(1+k)*σ-1-l) : ℝ) : EReal) := by
  have h := hpair.bourgain_density_long_cutoff hk hσ hσ1
    (div_pos hd hk) (by field_simp) hlong
  have he : 4/((2*(1+k)*σ-1-l)/k) = 4*k/(2*(1+k)*σ-1-l) := by
    field_simp
  simpa only [he] using h

end TaoTrudgianYang2025
