import DhimanKadiriQuesadaHerrera2026.TaylorLipschitz
import DhimanKadiriQuesadaHerrera2026.CurvatureExtension
import DhimanKadiriQuesadaHerrera2026.QuadraticStationary

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- Extending the actual curvature removes the central-window placement restriction completely. -/
theorem stationary_interval_bound_extended {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a < c) (hb : c < b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) +
        1 / Real.pi * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  have hab : a ≤ b := ha.le.trans hb.le
  have hcc : c ∈ Set.Icc a b := ⟨ha.le, hb.le⟩
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD c hcc)
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  let F := extendedPhase f a b hab c
  let A := min a (c - δ)
  let B := max b (c + δ)
  have hAa : A ≤ a := min_le_left _ _
  have hbB : b ≤ B := le_max_left _ _
  have hAm : A ≤ c - δ := min_le_right _ _
  have hpB : c + δ ≤ B := le_max_right _ _
  have hFc : F c = f c := extendedPhase_eq hab hcc hcc hf hf' hfc
  have hFd (u : ℝ) : HasDerivAt F (extendedSlope f a b hab c u) u := extendedPhase_hasDerivAt hab hfc c u
  have hFd_eq : deriv F = extendedSlope f a b hab c := funext fun u => (hFd u).deriv
  have hFdd (u : ℝ) : DifferentiableAt ℝ (deriv F) u := by
    rw [hFd_eq]
    exact (extendedSlope_hasDerivAt hab hfc c u).differentiableAt
  have hFderiv (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv F u = deriv f u := by
    rw [(hFd u).deriv]
    exact extendedSlope_eq hab hcc hu hf' hfc
  have hF2 (u : ℝ) : deriv (deriv F) u = extendedCurvature f a b hab u :=
    extendedPhase_second_deriv hab hfc c u
  have hF2c : deriv (deriv F) c = deriv (deriv f) c := (hF2 c).trans (extendedCurvature_eq hab hcc)
  have hFL (u : ℝ) : deriv (deriv F) u ≤ -ℓ := by
    rw [hF2]
    exact hcurv _ (Set.projIcc a b hab u).property
  have hflip (u : ℝ) : |deriv (deriv F) u - deriv (deriv F) c| ≤ D * |u - c| := by
    rw [hF2, hF2]
    exact extendedCurvature_lipschitz hab hf'' hD u c
  have hFanti : Antitone (deriv F) := by
    intro x y hxy
    have h := stationary_derivative_drop (fun u _ => hFdd u) (fun u _ => hFL u)
      (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    have hp := mul_nonneg hℓ.le (sub_nonneg.mpr hxy)
    linarith
  have hfa : ν < deriv f a := by
    have h := stationary_derivative_drop hf' hcurv haa hcc ha.le
    rw [hc] at h
    nlinarith [mul_pos hℓ (sub_pos.mpr ha)]
  have hfb : deriv f b < ν := by
    have h := stationary_derivative_drop hf' hcurv hcc hbb hb.le
    rw [hc] at h
    nlinarith [mul_pos hℓ (sub_pos.mpr hb)]
  have hmain := stationary_lipschitz_interval_window hDn hδ hℓ hAm hpB
    ((hFderiv c hcc).trans hc) (fun u _ => (hFd u).differentiableAt)
    (fun u _ => hFdd u) (fun u _ => hFL u) (fun u _ => hflip u)
  rw [hFc, hF2c] at hmain
  have hleft := norm_shifted_integral_positive hAa (fun u _ => (hFd u).differentiableAt)
    (fun u _ => (hFdd u).continuousAt.continuousWithinAt) (hFanti.antitoneOn _)
    (by rw [hFderiv a haa]; exact hfa)
  have hright := norm_shifted_integral_negative hbB (fun u _ => (hFd u).differentiableAt)
    (fun u _ => (hFdd u).continuousAt.continuousWithinAt) (hFanti.antitoneOn _)
    (by rw [hFderiv b hbb]; exact hfb)
  rw [hFderiv a haa] at hleft
  rw [hFderiv b hbb] at hright
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((F u - ν * u : ℝ) : ℂ))
  let M : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv f) c| : ℂ)
  have hK : Continuous K := by
    have hF : Continuous F := continuous_iff_continuousAt.mpr (fun u => (hFd u).continuousAt)
    dsimp [K]
    fun_prop
  have he : (∫ u in a..b, K u) - M =
      ((∫ u in A..B, K u) - M) - (∫ u in A..a, K u) - (∫ u in b..B, K u) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hK.intervalIntegrable (μ := volume) A a) (hK.intervalIntegrable a b)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hK.intervalIntegrable (μ := volume) A b) (hK.intervalIntegrable b B)
    linear_combination h1 + h2
  have heq : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) = ∫ u in a..b, K u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    dsimp [K, F]
    rw [extendedPhase_eq hab hcc hu hf hf' hfc]
  rw [heq]
  change ‖(∫ u in a..b, K u) - M‖ ≤ _
  rw [he]
  apply (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
  apply (add_le_add (add_le_add hmain hleft) hright).trans_eq
  rw [abs_of_pos (sub_pos.mpr hfa), abs_of_neg (sub_neg.mpr hfb)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The exact nonlinear stationary-phase bound holds at every interior stationary point, including zero third-derivative scale. -/
theorem stationary_phase_bound {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a < c) (hb : c < b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
        1 / Real.pi * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD c ⟨ha.le, hb.le⟩)
  rcases hDn.eq_or_lt with hzero | hpos
  · have hz : D = 0 := hzero.symm
    subst D
    have hthird (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv (deriv (deriv f)) u = 0 :=
      abs_nonpos_iff.mp (hD u hu)
    have hκ : deriv (deriv f) c < 0 := (hcurv c ⟨ha.le, hb.le⟩).trans_lt (neg_neg_of_pos hℓ)
    have h := stationary_zero_third_endpoint_bound ha hb hc hκ hf hf' hf'' hthird
    norm_num only [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), mul_zero, zero_div, zero_add]
    apply h.trans
    apply mul_le_mul_of_nonneg_right ?_ (by positivity)
    apply one_div_le_one_div_of_le Real.pi_pos
    linarith [Real.pi_pos]
  · let δ := (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
    have h := stationary_interval_bound_extended hδ hℓ ha hb hc hf hf' hf'' hcurv hD
    exact h.trans_eq (congrArg (fun z => z + 1 / Real.pi *
      (1 / |deriv f a - ν| + 1 / |deriv f b - ν|)) (stationary_radius_error_eq hpos hℓ))

/-- The stationary estimate retains the separated source scales h₃ and λ₃ with their exact powers. -/
theorem stationary_phase_source_scales {f : ℝ → ℝ} {a b c ν h₃ ℓ₂ ℓ₃ : ℝ}
    (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃)
    (ha : a < c) (hb : c < b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₃ ^ (1 / 3 : ℝ) *
        ℓ₃ ^ (1 / 3 : ℝ) / ℓ₂ +
        1 / Real.pi * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  apply (stationary_phase_bound hℓ₂ ha hb hc hf hf' hf'' hcurv hD).trans_eq
  rw [Real.mul_rpow hh₃ hℓ₃]
  ring

/-- Every frequency strictly inside the actual derivative range has a stationary point satisfying the full estimate. -/
theorem exists_stationary_phase_bound {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hνa : ν < deriv f a) (hνb : deriv f b < ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ c ∈ Set.Ioo a b, deriv f c = ν ∧
      ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
        Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
          1 / Real.pi * (1 / |deriv f a - ν| + 1 / |deriv f b - ν|) := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn (deriv f) (Set.Icc a b) := by
    intro x hx y hy hxy
    have hh := stationary_derivative_drop hf' hcurv hx hy hxy.le
    nlinarith [mul_pos hℓ (sub_pos.mpr hxy)]
  obtain ⟨c, hcc, _⟩ := existsUnique_stationaryPoint hab.le hfc hanti ⟨hνb.le, hνa.le⟩
  have hac : a < c := lt_of_le_of_ne hcc.1.1 (by intro he; subst c; linarith [hcc.2])
  have hcb : c < b := lt_of_le_of_ne hcc.1.2 (by intro he; subst c; linarith [hcc.2])
  exact ⟨c, ⟨hac, hcb⟩, hcc.2, stationary_phase_bound hℓ hac hcb hcc.2 hf hf' hf'' hcurv hD⟩

end DhimanKadiriQuesadaHerrera2026
