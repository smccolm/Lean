import DhimanKadiriQuesadaHerrera2026.AFEDigammaNumerics

/-! # Kernel-checked rational certificates for the two AFE1 decimal constants -/

namespace DhimanKadiriQuesadaHerrera2026

/-- Rational enclosure for the first scale at t₀=14.13472. -/
theorem afe_factor_certificate_small_first :
    afeFactorRationalUpper (1551455557 / 10000000000) ≤ (654700359 / 1000000000 : ℝ) := by
  norm_num [afeFactorRationalUpper, afeFactorRationalPart, logRationalUpper, logRationalLower,
    Finset.sum_range_succ]

/-- Rational enclosure for the upper-cell endpoint scale. -/
theorem afe_factor_certificate_small_second :
    afeFactorRationalUpper (1540209127 / 10000000000) ≤ (162732013 / 250000000 : ℝ) := by
  norm_num [afeFactorRationalUpper, afeFactorRationalPart, logRationalUpper, logRationalLower,
    Finset.sum_range_succ]

/-- Rational enclosure for the lower-cell endpoint scale. -/
theorem afe_factor_certificate_small_third :
    afeFactorRationalUpper (823215223 / 5000000000) ≤ (10729389 / 15625000 : ℝ) := by
  norm_num [afeFactorRationalUpper, afeFactorRationalPart, logRationalUpper, logRationalLower,
    Finset.sum_range_succ]

/-- One outward enclosure covers all three scales at t₀=3·10¹². -/
theorem afe_factor_certificate_large :
    afeFactorRationalUpper (1591549431 / 10000000000) ≤ (16704343 / 25000000 : ℝ) := by
  norm_num [afeFactorRationalUpper, afeFactorRationalPart, logRationalUpper, logRationalLower,
    Finset.sum_range_succ]

/-- The actual m(c) value for the small first source branch. -/
theorem afe_m_small_first_le :
    afeFirstConstant (90625 / 88342) 14.13472 ≤ 1.2552 := by
  have h := afeFirstConstant_le_rational_certificate (c := 90625 / 88342) (t₀ := 14.13472)
    (p := 31415926535 / 10000000000) (u := 1551455557 / 10000000000) (B := 654700359 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) afe_pi_lower (by norm_num) (by norm_num)
    afe_factor_certificate_small_first
  exact h.trans (by norm_num)

/-- The actual m(c) value for the small second source branch. -/
theorem afe_m_small_second_le :
    afeFirstConstant (31 / 30) 14.13472 ≤ 1.2552 := by
  have h := afeFirstConstant_le_rational_certificate (c := 31 / 30) (t₀ := 14.13472)
    (p := 31415926535 / 10000000000) (u := 1540209127 / 10000000000) (B := 162732013 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) afe_pi_lower (by norm_num) (by norm_num)
    afe_factor_certificate_small_second
  exact h.trans (by norm_num)

/-- The actual m(c) ratio for the small third source branch. -/
theorem afe_m_small_third_div_le :
    afeFirstConstant (29 / 30) 14.13472 / (29 / 30) ≤ 1.2552 := by
  have h := afeFirstConstant_le_rational_certificate (c := 29 / 30) (t₀ := 14.13472)
    (p := 31415926535 / 10000000000) (u := 823215223 / 5000000000) (B := 10729389 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) afe_pi_lower (by norm_num) (by norm_num)
    afe_factor_certificate_small_third
  apply (div_le_iff₀ (by norm_num)).mpr
  exact h.trans (by norm_num)

/-- The actual m(c) value for the large first source branch. -/
theorem afe_m_large_first_le :
    afeFirstConstant (6000000000001 / 6000000000000) 3000000000000 ≤ 1.2127 := by
  have h := afeFirstConstant_le_rational_certificate (c := 6000000000001 / 6000000000000) (t₀ := 3000000000000)
    (p := 31415926535 / 10000000000) (u := 1591549431 / 10000000000) (B := 16704343 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) afe_pi_lower (by norm_num) (by norm_num)
    afe_factor_certificate_large
  exact h.trans (by norm_num)

/-- The actual m(c) value for the large second source branch. -/
theorem afe_m_large_second_le :
    afeFirstConstant (6000000000003 / 6000000000002) 3000000000000 ≤ 1.2127 := by
  have h := afeFirstConstant_le_rational_certificate (c := 6000000000003 / 6000000000002) (t₀ := 3000000000000)
    (p := 31415926535 / 10000000000) (u := 1591549431 / 10000000000) (B := 16704343 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) afe_pi_lower (by norm_num) (by norm_num)
    afe_factor_certificate_large
  exact h.trans (by norm_num)

/-- The actual m(c) ratio for the large third source branch. -/
theorem afe_m_large_third_div_le :
    afeFirstConstant (6000000000001 / 6000000000002) 3000000000000 / (6000000000001 / 6000000000002) ≤ 1.2127 := by
  have h := afeFirstConstant_le_rational_certificate (c := 6000000000001 / 6000000000002) (t₀ := 3000000000000)
    (p := 31415926535 / 10000000000) (u := 1591549431 / 10000000000) (B := 16704343 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) afe_pi_lower (by norm_num) (by norm_num)
    afe_factor_certificate_large
  apply (div_le_iff₀ (by norm_num)).mpr
  exact h.trans (by norm_num)

/-- The exact source maximum c₀ at t₀=14.13472 satisfies the advertised decimal bound. -/
theorem afeFirstRealConstant_small_le : afeFirstRealConstant 14.13472 ≤ 1.2552 := by
  unfold afeFirstRealConstant
  rw [show ⌊(14.13472 : ℝ)⌋₊ = 14 by norm_num]
  dsimp only
  convert max_le (max_le afe_m_small_first_le afe_m_small_second_le)
    afe_m_small_third_div_le using 1
  norm_num

/-- The advertised 1.2552 real-cutoff AFE bound, with all analytic and numerical inputs discharged. -/
theorem afe_first_kind_small_decimal {sigma t : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht : 14.13472 ≤ t) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) t‖ ≤ 1.2552 * t ^ (-sigma) := by
  have h := afe_first_kind_real_cutoff hsigma (by norm_num : (14 : ℝ) ≤ 14.13472) ht
  exact h.trans (mul_le_mul_of_nonneg_right afeFirstRealConstant_small_le
    (Real.rpow_nonneg (by linarith) _))

/-- The exact source maximum c₀ at t₀=3000000000000 satisfies the advertised decimal bound. -/
theorem afeFirstRealConstant_large_le : afeFirstRealConstant 3000000000000 ≤ 1.2127 := by
  unfold afeFirstRealConstant
  rw [show ⌊(3000000000000 : ℝ)⌋₊ = 3000000000000 by norm_num]
  dsimp only
  convert max_le (max_le afe_m_large_first_le afe_m_large_second_le)
    afe_m_large_third_div_le using 1
  norm_num

/-- The advertised 1.2127 real-cutoff AFE bound, with all analytic and numerical inputs discharged. -/
theorem afe_first_kind_large_decimal {sigma t : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht : 3000000000000 ≤ t) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) t‖ ≤ 1.2127 * t ^ (-sigma) := by
  have h := afe_first_kind_real_cutoff hsigma (by norm_num : (14 : ℝ) ≤ 3000000000000) ht
  exact h.trans (mul_le_mul_of_nonneg_right afeFirstRealConstant_large_le
    (Real.rpow_nonneg (by linarith) _))

end DhimanKadiriQuesadaHerrera2026
