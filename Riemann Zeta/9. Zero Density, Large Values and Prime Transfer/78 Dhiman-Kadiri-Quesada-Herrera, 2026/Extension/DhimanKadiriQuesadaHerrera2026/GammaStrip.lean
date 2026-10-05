import DhimanKadiriQuesadaHerrera2026.GammaAnchors

/-! # An explicit Gamma bound on the closed half strip

The distance to the nearer exact anchor gives a uniform correction, including
the imaginary axis. No Stirling estimate is taken as a hypothesis.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex

/-- Squaring the horizontal comparison preserves its exact real-power factor. -/
theorem norm_Gamma_horizontal_sq_le {t a x : ℝ} (ht : 0 < t)
    (ha : a ∈ Set.Icc 0 (1 / 2 : ℝ)) (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ‖Gamma ((a : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        t ^ (2 * (x - a)) * Real.exp (|x - a| / t) := by
  have h := norm_Gamma_horizontal_le ht ha hx
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (t ^ (x - a)) 2,
    ← Real.rpow_mul ht.le, ← Real.exp_nat_mul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  rwa [show (x - a) * 2 = 2 * (x - a) by ring,
    show 2 * (|x - a| / (2 * t)) = |x - a| / t by ring] at hs

/-- The imaginary-axis anchor yields the left-hand half of the strip estimate. -/
theorem norm_Gamma_strip_sq_le_left {t x : ℝ} (ht : 1 / Real.pi ≤ t)
    (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * t ^ (2 * x - 1) * Real.exp (-Real.pi * t) *
        Real.exp (1 / (6 * t)) * Real.exp (x / t) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have h := norm_Gamma_horizontal_sq_le htpos (a := 0) (by norm_num) hx
  simp only [ofReal_zero, zero_add, sub_zero, abs_of_nonneg hx.1] at h
  have hp : t ^ (2 * x - 1) = t ^ (2 * x) / t := by
    rw [Real.rpow_sub htpos, Real.rpow_one]
  calc
    _ ≤ ‖Gamma ((t : ℂ) * I)‖ ^ 2 * t ^ (2 * x) * Real.exp (x / t) := h
    _ ≤ ((2 * Real.pi / t) * Real.exp (-Real.pi * t) * Real.exp (1 / (6 * t))) *
        t ^ (2 * x) * Real.exp (x / t) := by
      gcongr
      exact norm_Gamma_imag_sq_le ht
    _ = _ := by rw [hp]; ring

/-- The half-line anchor yields the right-hand half of the strip estimate. -/
theorem norm_Gamma_strip_sq_le_right {t x : ℝ} (ht : 0 < t)
    (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * t ^ (2 * x - 1) * Real.exp (-Real.pi * t) *
        Real.exp (1 / (6 * t)) * Real.exp ((1 / 2 - x) / t) := by
  have h := norm_Gamma_horizontal_sq_le ht (a := 1 / 2) (by norm_num) hx
  rw [abs_of_nonpos (by linarith [hx.2])] at h
  have he : 1 ≤ Real.exp (1 / (6 * t)) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : 2 * (x - 1 / 2) = 2 * x - 1 := by ring
  have hn : -(x - 1 / 2) = 1 / 2 - x := by ring
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [hp, hn] at h
  calc
    _ ≤ ‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        t ^ (2 * x - 1) * Real.exp ((1 / 2 - x) / t) := h
    _ ≤ (2 * Real.pi * Real.exp (-Real.pi * t)) *
        t ^ (2 * x - 1) * Real.exp ((1 / 2 - x) / t) := by
      gcongr
      exact norm_Gamma_half_add_imag_sq_le t
    _ ≤ _ := by
      have hm := mul_nonneg
        (show 0 ≤ 2 * Real.pi * t ^ (2 * x - 1) * Real.exp (-Real.pi * t) *
          Real.exp ((1 / 2 - x) / t) by positivity) (sub_nonneg.mpr he)
      nlinarith [hm]

/-- The nearer anchor gives the explicit uniform squared Gamma bound. -/
theorem norm_Gamma_strip_sq_le {t x : ℝ} (ht : 1 / Real.pi ≤ t)
    (hx : x ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * t ^ (2 * x - 1) * Real.exp (-Real.pi * t) *
        Real.exp (1 / (6 * t)) * Real.exp (min x (1 / 2 - x) / t) := by
  rcases le_total x (1 / 2 - x) with h | h
  · rw [min_eq_left h]
    exact norm_Gamma_strip_sq_le_left ht hx
  · rw [min_eq_right h]
    exact norm_Gamma_strip_sq_le_right (lt_of_lt_of_le (by positivity) ht) hx

end DhimanKadiriQuesadaHerrera2026
