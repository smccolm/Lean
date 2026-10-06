import DhimanKadiriQuesadaHerrera2026.StationaryTaylor
import DhimanKadiriQuesadaHerrera2026.FresnelSharp

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- Each positive half-window carries half of the stationary main term with its sharp tail. -/
theorem quadratic_half_window_sharp (A : ℝ) {κ H : ℝ} (hκ : κ < 0) (hH : 0 < H) :
    ‖(∫ x in (0 : ℝ)..H,
        Complex.exp (2 * Real.pi * Complex.I * ((A + κ * x ^ 2 / 2 : ℝ) : ℂ))) -
      (Complex.exp (2 * Real.pi * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ)) / 2‖ ≤ 1 / (2 * Real.pi * |κ| * H) := by
  let K : ℝ → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * ((A + κ * x ^ 2 / 2 : ℝ) : ℂ))
  let M : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |κ| : ℂ)
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hn (x : ℝ) : K (-x) = K x := by simp [K]
  have hleft : (∫ x in (-H)..0, K x) = ∫ x in (0 : ℝ)..H, K x := by
    simpa only [hn, neg_zero, neg_neg] using intervalIntegral.integral_comp_neg K (a := -H) (b := 0)
  have he : (∫ x in (-H)..H, K x) - M = 2 * ((∫ x in (0 : ℝ)..H, K x) - M / 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hK.intervalIntegrable _ _) (hK.intervalIntegrable _ _), hleft]
    ring
  have h := quadratic_stationary_phase_sharp A hκ hH
  change ‖(∫ x in (-H)..H, K x) - M‖ ≤ _ at h
  rw [he, norm_mul, Complex.norm_ofNat] at h
  change ‖(∫ x in (0 : ℝ)..H, K x) - M / 2‖ ≤ _
  have hb : 1 / (Real.pi * |κ| * H) = 2 * (1 / (2 * Real.pi * |κ| * H)) := by ring
  rw [hb] at h
  linarith

/-- Unequal endpoint distances retain both sharp quadratic tails separately. -/
theorem quadratic_asymmetric_stationary_sharp (A : ℝ) {κ a b : ℝ}
    (hκ : κ < 0) (ha : a < 0) (hb : 0 < b) :
    ‖(∫ x in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((A + κ * x ^ 2 / 2 : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |κ| : ℂ)‖ ≤
      1 / (2 * Real.pi * |κ| * (-a)) + 1 / (2 * Real.pi * |κ| * b) := by
  let K : ℝ → ℂ := fun x => Complex.exp (2 * Real.pi * Complex.I * ((A + κ * x ^ 2 / 2 : ℝ) : ℂ))
  let M : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((A - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |κ| : ℂ)
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hn (x : ℝ) : K (-x) = K x := by simp [K]
  have hleft : (∫ x in a..0, K x) = ∫ x in (0 : ℝ)..(-a), K x := by
    simpa only [hn, neg_zero] using intervalIntegral.integral_comp_neg K (a := a) (b := 0)
  have he : (∫ x in a..b, K x) - M =
      ((∫ x in (0 : ℝ)..(-a), K x) - M / 2) + ((∫ x in (0 : ℝ)..b, K x) - M / 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hK.intervalIntegrable _ _) (hK.intervalIntegrable _ _), hleft]
    ring
  change ‖(∫ x in a..b, K x) - M‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (quadratic_half_window_sharp A hκ (by linarith))
    (quadratic_half_window_sharp A hκ hb))

/-- A vanishing third derivative gives the full stationary estimate at arbitrary interior points. -/
theorem stationary_zero_third_bound {f : ℝ → ℝ} {a b c ν : ℝ}
    (ha : a < c) (hb : c < b) (hc : deriv f c = ν) (hκ : deriv (deriv f) c < 0)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hthird : ∀ u ∈ Set.Icc a b, deriv (deriv (deriv f)) u = 0) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      1 / (2 * Real.pi * |deriv (deriv f) c| * (c - a)) +
        1 / (2 * Real.pi * |deriv (deriv f) c| * (b - c)) := by
  have hseg (u : ℝ) (hu : u ∈ Set.Icc a b) : Set.uIcc c u ⊆ Set.Icc a b :=
    Set.uIcc_subset_Icc ⟨ha.le, hb.le⟩ hu
  have he (u : ℝ) (hu : u ∈ Set.Icc a b) :
      f u - ν * u = f c - ν * c + deriv (deriv f) c * (u - c) ^ 2 / 2 := by
    have ht := quadratic_taylor_remainder_bound (fun x hx => hf x (hseg u hu hx))
      (fun x hx => hf' x (hseg u hu hx)) (fun x hx => hf'' x (hseg u hu hx))
      (D := 0) (fun x hx => by rw [hthird x (hseg u hu hx)]; simp)
    simp only [zero_mul, zero_div, abs_nonpos_iff, hc] at ht
    nlinarith
  have hi : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) =
      ∫ x in (a - c)..(b - c),
        Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c + deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c + deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ))) c]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (ha.le.trans hb.le)] at hu
    dsimp only
    rw [he u hu]
  rw [hi]
  convert quadratic_asymmetric_stationary_sharp (f c - ν * c) hκ
    (sub_neg.mpr ha) (sub_pos.mpr hb) using 1
  congr 3
  ring

/-- With zero third derivative the actual frequency gap is exactly curvature times displacement. -/
theorem stationary_zero_third_derivative {f : ℝ → ℝ} {a b c ν u : ℝ}
    (hcc : c ∈ Set.Icc a b) (hu : u ∈ Set.Icc a b) (hc : deriv f c = ν)
    (hf' : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) x)
    (hf'' : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) x)
    (hthird : ∀ x ∈ Set.Icc a b, deriv (deriv (deriv f)) x = 0) :
    deriv f u - ν = (u - c) * deriv (deriv f) c := by
  have hs : Set.uIcc c u ⊆ Set.Icc a b := Set.uIcc_subset_Icc hcc hu
  have h := derivative_taylor_remainder_bound (fun x hx => hf' x (hs hx))
    (fun x hx => hf'' x (hs hx)) (D := 0) (fun x hx => by rw [hthird x (hs hx)]; simp)
  simp only [zero_mul, zero_div, abs_nonpos_iff, hc] at h
  linarith

/-- The zero-third-derivative case has the exact endpoint-frequency remainder without a radius restriction. -/
theorem stationary_zero_third_endpoint_bound {f : ℝ → ℝ} {a b c ν : ℝ}
    (ha : a < c) (hb : c < b) (hc : deriv f c = ν) (hκ : deriv (deriv f) c < 0)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hthird : ∀ u ∈ Set.Icc a b, deriv (deriv (deriv f)) u = 0) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      1 / (2 * Real.pi) * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  have hcc : c ∈ Set.Icc a b := ⟨ha.le, hb.le⟩
  have hqa := stationary_zero_third_derivative hcc (Set.left_mem_Icc.mpr (ha.le.trans hb.le)) hc hf' hf'' hthird
  have hqb := stationary_zero_third_derivative hcc (Set.right_mem_Icc.mpr (ha.le.trans hb.le)) hc hf' hf'' hthird
  have hae : |deriv f a - ν| = |deriv (deriv f) c| * (c - a) := by
    rw [hqa, abs_mul, abs_of_neg (sub_neg.mpr ha)]
    ring
  have hbe : |deriv f b - ν| = |deriv (deriv f) c| * (b - c) := by
    rw [hqb, abs_mul, abs_of_pos (sub_pos.mpr hb)]
    ring
  rw [hae, hbe]
  apply (stationary_zero_third_bound ha hb hc hκ hf hf' hf'' hthird).trans_eq
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end DhimanKadiriQuesadaHerrera2026

