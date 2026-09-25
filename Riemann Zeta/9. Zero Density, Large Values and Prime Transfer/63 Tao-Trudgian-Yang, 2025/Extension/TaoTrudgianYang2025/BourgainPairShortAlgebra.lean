import TaoTrudgianYang2025.BourgainPairLongCutoff

/-! Exact parameter algebra for the complementary restricted-sixth branch. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem bourgain_short_cutoff_threshold {k l σ t : ℝ}
    (hk : 0 < k) (hkfifth : k < 1/5)
    (hpairrange : 13 < 15*l+20*k)
    (hscale : k*t = 2*(1+k)*σ-1-l)
    (hshort : t ≤ 12*σ-8)
    (hside : k < 11/85 ∨
      (11/85 < k ∧ (144*k-11*l-11)/(170*k-22) < σ)) :
    (11/72)*(3*t/4) < 2*σ-3/2 := by
  have hd : 0 < 2-10*k := by linarith
  have htarget : 0 < (170*k-22)*σ-144*k+11*l+11 := by
    rcases hside with hsmall | ⟨hlarge,hσ⟩
    · have hA : 0 < 22-170*k := by linarith
      have hu : (2-10*k)*σ ≤ 1+l-8*k := by
        have hm := mul_le_mul_of_nonneg_left hshort hk.le
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hu hA.le
      have hp := mul_pos hk (show 0 < 15*l+20*k-13 by linarith)
      have he : (2-10*k)*((170*k-22)*σ-144*k+11*l+11) =
          4*k*(15*l+20*k-13) +
          (22-170*k)*((1+l-8*k)-(2-10*k)*σ) := by ring
      have hn : 0 ≤ (22-170*k)*((1+l-8*k)-(2-10*k)*σ) :=
        mul_nonneg hA.le (sub_nonneg.mpr hu)
      have hpos : 0 < (2-10*k)*((170*k-22)*σ-144*k+11*l+11) := by
        rw [he]
        nlinarith
      exact (mul_pos_iff_of_pos_left hd).mp hpos
    · have hden : 0 < 170*k-22 := by linarith
      have hh := (div_lt_iff₀ hden).mp hσ
      nlinarith
  have he : k*(192*σ-144-11*t) =
      (170*k-22)*σ-144*k+11*l+11 := by nlinarith [hscale]
  have hg : 0 < 192*σ-144-11*t := by
    apply (mul_pos_iff_of_pos_left hk).mp
    rwa [he]
  linarith

theorem bourgain_short_cutoff_affine_budget {σ t τ : ℝ}
    (hσ : 3/4 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 < t)
    (hshort : t ≤ 12*σ-8) (hτlo : t/2 ≤ τ) (hτhi : τ ≤ 3*t/4) :
    max (2-2*σ) (τ+9-12*σ) ≤ (3-3*σ)*τ/(3*t/4) := by
  have hτ : 0 ≤ τ := by linarith
  have hf : 2-2*σ ≤ (3-3*σ)*τ/(3*t/4) := by
    apply (le_div_iff₀ (by positivity : 0 < 3*t/4)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (sub_nonneg.mpr hτlo)]
  have hs : τ+9-12*σ ≤ (3-3*σ)*τ/(3*t/4) := by
    apply (le_div_iff₀ (by positivity : 0 < 3*t/4)).mpr
    by_cases htB : 4*(1-σ) ≤ t
    · have hm := mul_nonneg (sub_nonneg.mpr htB) (sub_nonneg.mpr hτhi)
      have hn := mul_nonneg ht.le (show 0 ≤ 12*σ-8-t by linarith)
      nlinarith
    · have hm := mul_nonneg hτ (show 0 ≤ 4*(1-σ)-t by linarith)
      have hn := mul_nonneg ht.le (show 0 ≤ 12*σ-9 by linarith)
      nlinarith
  exact max_le hf hs

end TaoTrudgianYang2025
