import TaoTrudgianYang2025.AtkinsonGapExponentPair

/-! The true Atkinson gap frequency has uniform physical square-root scales. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem atkinsonGap_denominator_bounds {H M t u : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hu : H ≤ u) (hu2 : u ≤ 2*H)
    (ht : u < t) (ht2 : t ≤ 2*u) :
    Real.sqrt (H*M) ≤
        M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1) ∧
      M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1) ≤
        12*Real.sqrt (H*M) := by
  have hup : 0 < u := hH.trans_le hu
  have htp : 0 < t := hup.trans ht
  have hs : 0 < Real.sqrt (2*Real.pi*u/M) := by positivity
  have hR : 0 < Real.sqrt (H*M) := by positivity
  have ha : 0 < M*Real.sqrt (2*Real.pi*u/M) := mul_pos hM hs
  have he : (M*Real.sqrt (2*Real.pi*u/M))^2 = 2*Real.pi*M*u := by
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi*u/M)]
    field_simp
  have hR2 := Real.sq_sqrt (show 0 ≤ H*M by positivity)
  have hl : H ≤ 2*Real.pi*u := by
    have hp : 0 ≤ (2*Real.pi-1)*u :=
      mul_nonneg (by linarith [Real.pi_gt_three]) hup.le
    linarith
  have hpiu : Real.pi*u ≤ 8*H := by
    have h := mul_le_mul Real.pi_lt_four.le hu2 hup.le (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hal : Real.sqrt (H*M) ≤ M*Real.sqrt (2*Real.pi*u/M) := by
    have hh := mul_le_mul_of_nonneg_right hl hM.le
    nlinarith
  have hau : M*Real.sqrt (2*Real.pi*u/M) ≤ 4*Real.sqrt (H*M) := by
    have hh := mul_le_mul_of_nonneg_left hpiu (show 0 ≤ 2*M by positivity)
    nlinarith
  have hr : t/u ≤ 2 := (div_le_iff₀ hup).mpr ht2
  have hrs : Real.sqrt (t/u) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by linarith⟩
  constructor
  · exact hal.trans (le_mul_of_one_le_right ha.le (by linarith [Real.sqrt_nonneg (t/u)]))
  · calc
      _ ≤ (4*Real.sqrt (H*M))*3 :=
        mul_le_mul hau (by linarith : Real.sqrt (t/u)+1 ≤ 3)
          (by positivity) (by positivity)
      _ = _ := by ring

theorem atkinsonGap_frequency_physical_bounds {H M t u : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hu : H ≤ u) (hu2 : u ≤ 2*H)
    (ht : u < t) (ht2 : t ≤ 2*u) :
    atkinsonGapFrequency M t u/(2*Real.pi*M) ≤ (t-u)/Real.sqrt (H*M) ∧
      2*Real.pi*M/atkinsonGapFrequency M t u ≤
        12*Real.sqrt (H*M)/(t-u) := by
  have hup : 0 < u := hH.trans_le hu
  have hgap : 0 < t-u := sub_pos.mpr ht
  have hR : 0 < Real.sqrt (H*M) := by positivity
  have hs : 0 < Real.sqrt (2*Real.pi*u/M) := by positivity
  obtain ⟨hl,hh⟩ := atkinsonGap_denominator_bounds hH hM hu hu2 ht ht2
  have he : atkinsonGapFrequency M t u/(2*Real.pi*M) =
      (t-u)/(M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1)) := by
    unfold atkinsonGapFrequency
    field_simp
  have he' : 2*Real.pi*M/atkinsonGapFrequency M t u =
      (M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1))/(t-u) := by
    unfold atkinsonGapFrequency
    field_simp
  rw [he,he']
  exact ⟨div_le_div_of_nonneg_left hgap.le hR hl,
    div_le_div_of_nonneg_right hh hgap.le⟩

end TaoTrudgianYang2025
