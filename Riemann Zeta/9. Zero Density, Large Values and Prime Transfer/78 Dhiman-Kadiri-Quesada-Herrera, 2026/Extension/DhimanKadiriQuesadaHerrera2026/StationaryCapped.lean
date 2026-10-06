import DhimanKadiriQuesadaHerrera2026.KershnerHalf

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- Extending the actual curvature removes the central-window placement restriction completely. -/
theorem stationary_interval_bound_capped {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) +
        1.343 / Real.sqrt ℓ := by
  have hab : a ≤ b := ha.trans hb
  have hcc : c ∈ Set.Icc a b := ⟨ha, hb⟩
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
  have hmain := stationary_lipschitz_interval_window hDn hδ hℓ hAm hpB
    ((hFderiv c hcc).trans hc) (fun u _ => (hFd u).differentiableAt)
    (fun u _ => hFdd u) (fun u _ => hFL u) (fun u _ => hflip u)
  rw [hFc, hF2c] at hmain
  have hleft := kershner_monotone_global hAa hℓ (fun u => (hFd u).differentiableAt) hFdd
    (fun u _ => hFL u) ν (Or.inl (fun u hu => by
      rw [← hc, ← hFderiv c hcc]
      exact hFanti (hu.2.trans ha)))
  have hright := kershner_monotone_global hbB hℓ (fun u => (hFd u).differentiableAt) hFdd
    (fun u _ => hFL u) ν (Or.inr (fun u hu => by
      rw [← hc, ← hFderiv c hcc]
      exact hFanti (hb.trans hu.1)))
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
  ring

/-- A finite stationary estimate with no endpoint pole includes stationary points at either endpoint and the zero-third-derivative case. -/
theorem stationary_phase_capped {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
        1.343 / Real.sqrt ℓ := by
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD c ⟨ha, hb⟩)
  rcases hDn.eq_or_lt with hzero | hpos
  · have hz : D = 0 := hzero.symm
    subst D
    norm_num only [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), mul_zero, zero_div, zero_add]
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := 3 / (Real.pi * ℓ * ε)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h := stationary_interval_bound_capped hδ hℓ ha hb hc hf hf' hf'' hcurv hD
    norm_num only [zero_mul, zero_div, zero_add] at h
    apply h.trans_eq
    dsimp [δ]
    field_simp
    ring
  · let δ := (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
    exact (stationary_interval_bound_capped hδ hℓ ha hb hc hf hf' hf'' hcurv hD).trans_eq
      (congrArg (fun z => z + 1.343 / Real.sqrt ℓ) (stationary_radius_error_eq hpos hℓ))

/-- The curvature cap stays finite at an endpoint stationary point and uses the derivative gap elsewhere. -/
noncomputable def stationaryEndpointCap (ℓ gap : ℝ) : ℝ :=
  if gap = 0 then 0.6715 / Real.sqrt ℓ else min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * |gap|))

/-- A positive-slope tail simultaneously obeys the first- and second-derivative estimates. -/
theorem kershner_positive_gap {f : ℝ → ℝ} {a b ℓ ν : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hm : Antitone (deriv f)) (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hpos : ν ≤ deriv f b) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      stationaryEndpointCap ℓ (deriv f b - ν) := by
  have hh := kershner_monotone_global hab hℓ hf hf' hcurv ν
    (Or.inl (fun u hu => hpos.trans (hm hu.2)))
  by_cases hz : deriv f b - ν = 0
  · simpa only [stationaryEndpointCap, if_pos hz] using hh
  · rw [stationaryEndpointCap, if_neg hz]
    apply le_min hh
    have hp : ν < deriv f b := lt_of_le_of_ne hpos (by intro he; exact hz (by linarith))
    rw [abs_of_pos (sub_pos.mpr hp)]
    exact norm_shifted_integral_positive hab (fun u _ => hf u) hf'.continuous.continuousOn
      (hm.antitoneOn _) hp

/-- A negative-slope tail has the symmetric finite gap cap. -/
theorem kershner_negative_gap {f : ℝ → ℝ} {a b ℓ ν : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hm : Antitone (deriv f)) (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hneg : deriv f a ≤ ν) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      stationaryEndpointCap ℓ (deriv f a - ν) := by
  have hh := kershner_monotone_global hab hℓ hf hf' hcurv ν
    (Or.inr (fun u hu => (hm hu.1).trans hneg))
  by_cases hz : deriv f a - ν = 0
  · simpa only [stationaryEndpointCap, if_pos hz] using hh
  · rw [stationaryEndpointCap, if_neg hz]
    apply le_min hh
    have hn : deriv f a < ν := lt_of_le_of_ne hneg (by intro he; exact hz (by linarith))
    rw [abs_of_neg (sub_neg.mpr hn), neg_sub]
    exact norm_shifted_integral_negative hab (fun u _ => hf u) hf'.continuous.continuousOn
      (hm.antitoneOn _) hn
/-- Extending the actual curvature removes the central-window placement restriction completely. -/
theorem stationary_interval_bound_gap {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) +
        stationaryEndpointCap ℓ (deriv f a - ν) + stationaryEndpointCap ℓ (deriv f b - ν) := by
  have hab : a ≤ b := ha.trans hb
  have hcc : c ∈ Set.Icc a b := ⟨ha, hb⟩
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
  have hmain := stationary_lipschitz_interval_window hDn hδ hℓ hAm hpB
    ((hFderiv c hcc).trans hc) (fun u _ => (hFd u).differentiableAt)
    (fun u _ => hFdd u) (fun u _ => hFL u) (fun u _ => hflip u)
  rw [hFc, hF2c] at hmain
  have hleft := kershner_positive_gap (ν := ν) hAa hℓ (fun u => (hFd u).differentiableAt) hFdd hFanti
    (fun u _ => hFL u) (by
      rw [← hc, ← hFderiv c hcc]
      exact hFanti ha)
  have hright := kershner_negative_gap (ν := ν) hbB hℓ (fun u => (hFd u).differentiableAt) hFdd hFanti
    (fun u _ => hFL u) (by
      rw [← hc, ← hFderiv c hcc]
      exact hFanti hb)
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
  ring

/-- A finite stationary estimate with no endpoint pole includes stationary points at either endpoint and the zero-third-derivative case. -/
theorem stationary_phase_gap_bound {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
        stationaryEndpointCap ℓ (deriv f a - ν) + stationaryEndpointCap ℓ (deriv f b - ν) := by
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD c ⟨ha, hb⟩)
  rcases hDn.eq_or_lt with hzero | hpos
  · have hz : D = 0 := hzero.symm
    subst D
    norm_num only [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), mul_zero, zero_div, zero_add]
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := 3 / (Real.pi * ℓ * ε)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h := stationary_interval_bound_gap hδ hℓ ha hb hc hf hf' hf'' hcurv hD
    norm_num only [zero_mul, zero_div, zero_add] at h
    apply h.trans_eq
    have he : 3 / (Real.pi * ℓ * δ) = ε := by
      dsimp [δ]
      field_simp
    rw [he]
    ring
  · let δ := (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
    exact (stationary_interval_bound_gap hδ hℓ ha hb hc hf hf' hf'' hcurv hD).trans_eq
      (congrArg (fun z => z + stationaryEndpointCap ℓ (deriv f a - ν) + stationaryEndpointCap ℓ (deriv f b - ν)) (stationary_radius_error_eq hpos hℓ))


end DhimanKadiriQuesadaHerrera2026
