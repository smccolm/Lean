import TaoTrudgianYang2025.BourgainPairShortAlgebra
import TaoTrudgianYang2025.BourgainPairZeroCoordinate
import TaoTrudgianYang2025.IvicSixthGeneralLargeValues

/-! Bourgain's complementary short branch and complete pair-to-density theorem. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem ExponentPair.bourgain_density_short_cutoff {k l σ t : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hσ : 1/2 < σ) (hσ1 : σ < 1) (ht : 0 < t)
    (hscale : k*t = 2*(1+k)*σ-1-l)
    (hshort : t ≤ 12*σ-8) (hgap : (11/72)*(3*t/4) < 2*σ-3/2) :
    zeroDensityExponent σ ≤ ((4/t:ℝ):EReal) := by
  by_cases hlow : σ ≤ 4/5
  · apply (zeroDensityExponent_le_ingham hσ hσ1.le).trans
    apply EReal.coe_le_coe_iff.mpr
    apply (div_le_div_iff₀ (by linarith : 0 < 2-σ) ht).mpr
    nlinarith
  have hout := zeroDensityExponent_le_three_div_of_largeValue_bounds
    σ (3*t/4) hσ hσ1 (by positivity)
  have hz : ∀ τ ∈ Set.Ico (2:ℝ) (4*(3*t/4)/3),
      zetaLargeValueExponent σ τ ≤ (((3-3*σ)*τ/(3*t/4):ℝ):EReal) := by
    intro τ hτ
    rw [hpair.aProcess_zeta_cutoff hk hσ.le (by linarith [hτ.1])
      (by linarith [hτ.2]) hscale]
    exact bot_le
  have hg : ∀ τ ∈ Set.Icc (2*(3*t/4)/3) (3*t/4),
      largeValueExponent σ τ ≤ (((3-3*σ)*τ/(3*t/4):ℝ):EReal) := by
    intro τ hτ
    have hτp : 0 < τ := by linarith [hτ.1]
    have hthreshold : (11/72)*τ < 2*σ-3/2 := by linarith [hτ.2]
    apply (ivicSixth_general_largeValueExponent_le hτp hthreshold).trans
    apply EReal.coe_le_coe_iff.mpr
    exact bourgain_short_cutoff_affine_budget (by linarith) hσ1.le ht hshort
      (by linarith [hτ.1]) hτ.2
  have hb := hout hz hg
  have he : 3/(3*t/4) = 4/t := by field_simp
  simpa only [he] using hb

theorem zeroDensityExponent_at_one_le (B : ℝ) :
    zeroDensityExponent 1 ≤ (B:EReal) := by
  have hi := ingham_isZeroDensityBound (σ := 1) (by norm_num) le_rfl
  have hb : IsZeroDensityBound 1 B := by
    simpa only [IsZeroDensityBound,sub_self,mul_zero] using hi
  exact zeroDensityExponent_le_of_bound hb

/-- The printed Bourgain pair-to-density theorem on the closed right
endpoint of the density strip, including the zero first coordinate. -/
theorem ExponentPair.bourgain_zero_density {k l σ : ℝ}
    (hpair : ExponentPair k l)
    (hk : k < 1/5) (hl : 3/5 < l) (hrange : 13 < 15*l+20*k)
    (hline : (l+1)/(2*(k+1)) < σ) (hσ1 : σ ≤ 1)
    (hside : k < 11/85 ∨
      (11/85 < k ∧ (144*k-11*l-11)/(170*k-22) < σ)) :
    zeroDensityExponent σ ≤ ((4*k/(2*(1+k)*σ-1-l):ℝ):EReal) := by
  have hk0 : 0 ≤ k := hpair.inTriangle.1
  have hden : 0 < 2*(k+1) := by linarith
  have hline' := (div_lt_iff₀ hden).mp hline
  have hkl : k < l := by linarith only [hk,hl]
  have hσ : 1/2 < σ := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hden.le
    nlinarith only [hline',hm,hkl]
  by_cases heq : σ = 1
  · subst σ
    exact zeroDensityExponent_at_one_le _
  have hσlt : σ < 1 := lt_of_le_of_ne hσ1 heq
  by_cases hkz : k = 0
  · subst k
    have hz := hpair.zero_first_coordinate_density hσ hσlt (by simpa using hline)
    simpa only [mul_zero,zero_mul,zero_div,EReal.coe_zero] using hz
  have hkp : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hkz)
  have hd : 0 < 2*(1+k)*σ-1-l := by nlinarith
  let t : ℝ := (2*(1+k)*σ-1-l)/k
  have ht : 0 < t := div_pos hd hkp
  have hscale : k*t = 2*(1+k)*σ-1-l := by dsimp [t]; field_simp
  have hb : zeroDensityExponent σ ≤ ((4/t:ℝ):EReal) := by
    by_cases hlong : 12*σ-8 ≤ t
    · exact hpair.bourgain_density_long_cutoff hkp hσ hσlt ht hscale hlong
    · have hshort : t ≤ 12*σ-8 := (lt_of_not_ge hlong).le
      exact hpair.bourgain_density_short_cutoff hkp hσ hσlt ht hscale hshort
        (bourgain_short_cutoff_threshold hkp hk hrange hscale hshort hside)
  have he : 4/t = 4*k/(2*(1+k)*σ-1-l) := by dsimp [t]; field_simp
  simpa only [he] using hb

end TaoTrudgianYang2025
