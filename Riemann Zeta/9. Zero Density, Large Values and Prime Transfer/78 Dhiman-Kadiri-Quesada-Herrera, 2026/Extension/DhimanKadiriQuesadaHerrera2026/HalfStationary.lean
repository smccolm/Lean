import DhimanKadiriQuesadaHerrera2026.StationaryHalf

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- A contained one-sided window has exactly half the nonlinear stationary error. -/
theorem stationary_half_window_global {f : ℝ → ℝ} {c b ν δ D ℓ : ℝ}
    (hDn : 0 ≤ D) (hδ : 0 < δ) (hℓ : 0 < ℓ) (hb : c + δ ≤ b) (hc : deriv f c = ν)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u, deriv (deriv f) u ≤ -ℓ)
    (hL : ∀ u, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in c..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      D * δ ^ 2 / (2 * ℓ) + 3 / (2 * Real.pi * ℓ * δ) := by
  have hκ : deriv (deriv f) c < 0 := (hcurv c).trans_lt (neg_neg_of_pos hℓ)
  have hk : ℓ ≤ |deriv (deriv f) c| := by rw [abs_of_neg hκ]; linarith [hcurv c]
  have hcentral := stationary_half_fresnel_lipschitz hδ hκ hc
    (fun u _ => hf u) (fun u _ => hf' u) (fun u _ => hL u)
  have hC : ‖(∫ u in c..(c + δ), Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      D * δ ^ 2 / (2 * ℓ) + 1 / (2 * Real.pi * ℓ * δ) := hcentral.trans (add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith : 2 * ℓ ≤ 2 * |deriv (deriv f) c|))
        (one_div_le_one_div_of_le (by positivity) (by nlinarith [mul_pos Real.pi_pos hδ])))
  have hm : Antitone (deriv f) := by
    intro x y hxy
    have hh := stationary_derivative_drop (fun u _ => hf' u) (fun u _ => hcurv u)
      (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    nlinarith [mul_nonneg hℓ.le (sub_nonneg.mpr hxy)]
  have hslope : ℓ * δ ≤ ν - deriv f (c + δ) := by
    have hh := stationary_derivative_drop (fun u _ => hf' u) (fun u _ => hcurv u)
      (Set.left_mem_Icc.mpr (by linarith : c ≤ c + δ))
      (Set.right_mem_Icc.mpr (by linarith : c ≤ c + δ)) (by linarith : c ≤ c + δ)
    rw [hc] at hh
    linarith
  have ht := norm_shifted_integral_negative hb (fun u _ => hf u) hf'.continuous.continuousOn
    (hm.antitoneOn _) (by nlinarith [mul_pos hℓ hδ] : deriv f (c + δ) < ν)
  have hT : ‖∫ u in (c + δ)..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * ℓ * δ) := ht.trans (one_div_le_one_div_of_le (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hslope Real.pi_pos.le]))
  have hK : Continuous (fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) := by
    have hfc := hf.continuous
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hK.intervalIntegrable (μ := volume) c (c + δ))
    (hK.intervalIntegrable (c + δ) b)]
  rw [show (∫ u in c..(c + δ), Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) +
      (∫ u in (c + δ)..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2 =
      ((∫ u in c..(c + δ), Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2) +
      (∫ u in (c + δ)..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) by ring]
  exact (norm_add_le _ _).trans ((add_le_add hC hT).trans_eq (by ring))


/-- Enlarging only the right endpoint gives the exact half error plus its single finite endpoint cap. -/
theorem stationary_right_window_global {f : ℝ → ℝ} {c b ν δ D ℓ : ℝ}
    (hDn : 0 ≤ D) (hδ : 0 < δ) (hℓ : 0 < ℓ) (hcb : c ≤ b) (hc : deriv f c = ν)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u, deriv (deriv f) u ≤ -ℓ)
    (hL : ∀ u, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in c..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      D * δ ^ 2 / (2 * ℓ) + 3 / (2 * Real.pi * ℓ * δ) + stationaryEndpointCap ℓ (deriv f b - ν) := by
  let B := max b (c + δ)
  have hbB : b ≤ B := le_max_left _ _
  have hmain := stationary_half_window_global hDn hδ hℓ (le_max_right b (c + δ)) hc hf hf' hcurv hL
  have hm : Antitone (deriv f) := by
    intro x y hxy
    have hh := stationary_derivative_drop (fun u _ => hf' u) (fun u _ => hcurv u)
      (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    nlinarith [mul_nonneg hℓ.le (sub_nonneg.mpr hxy)]
  have ht := kershner_negative_gap (ν := ν) hbB hℓ hf hf' hm (fun u _ => hcurv u)
    ((hm hcb).trans_eq hc)
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  let P := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
    (Real.sqrt |deriv (deriv f) c| : ℂ) / 2
  have hK : Continuous K := by have hfc := hf.continuous; dsimp [K]; fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) c b) (hK.intervalIntegrable b B)
  have he : (∫ u in c..b, K u) - P = ((∫ u in c..B, K u) - P) - (∫ u in b..B, K u) := by rw [← hi]; ring
  change ‖(∫ u in c..b, K u) - P‖ ≤ _
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hmain ht)

/-- Optimizing the one-sided radius gives exactly half the source nonlinear coefficient, also when the third-derivative scale is zero. -/
theorem stationary_right_lipschitz_global {f : ℝ → ℝ} {c b ν D ℓ : ℝ}
    (hDn : 0 ≤ D) (hℓ : 0 < ℓ) (hcb : c ≤ b) (hc : deriv f c = ν)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u, deriv (deriv f) u ≤ -ℓ)
    (hL : ∀ u, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in c..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f b - ν) := by
  rcases hDn.eq_or_lt with hz | hpos
  · have he : D = 0 := hz.symm
    subst D
    norm_num only [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), mul_zero, zero_div, zero_add]
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := 3 / (2 * Real.pi * ℓ * ε)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h := stationary_right_window_global hDn hδ hℓ hcb hc hf hf' hcurv hL
    norm_num only [zero_mul, zero_div, zero_add] at h
    apply h.trans_eq
    have he : 3 / (2 * Real.pi * ℓ * δ) = ε := by dsimp [δ]; field_simp
    rw [he]
    ring
  · let δ := (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
    have h := stationary_right_window_global hDn hδ hℓ hcb hc hf hf' hcurv hL
    apply h.trans_eq
    have he : D * δ ^ 2 / (2 * ℓ) + 3 / (2 * Real.pi * ℓ * δ) =
        ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 := by
      calc
        _ = (D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ)) / 2 := by ring
        _ = _ := congrArg (fun z => z / 2) (stationary_radius_error_eq hpos hℓ)
    rw [he]


/-- The source derivatives give the right-hand half stationary estimate with its single endpoint cap. -/
theorem stationary_right_phase_bound {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (ha : deriv f a = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) a| : ℂ) / 2‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f b - ν) := by
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  let F := extendedPhase f a b hab a
  have hFd (u : ℝ) : HasDerivAt F (extendedSlope f a b hab a u) u := extendedPhase_hasDerivAt hab hfc a u
  have hFd_eq : deriv F = extendedSlope f a b hab a := funext fun u => (hFd u).deriv
  have hFdd (u : ℝ) : DifferentiableAt ℝ (deriv F) u := by
    rw [hFd_eq]
    exact (extendedSlope_hasDerivAt hab hfc a u).differentiableAt
  have hFderiv (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv F u = deriv f u := by
    rw [(hFd u).deriv]
    exact extendedSlope_eq hab haa hu hf' hfc
  have hF2 (u : ℝ) : deriv (deriv F) u = extendedCurvature f a b hab u :=
    extendedPhase_second_deriv hab hfc a u
  have hFL (u : ℝ) : deriv (deriv F) u ≤ -ℓ := by
    rw [hF2]
    exact hcurv _ (Set.projIcc a b hab u).property
  have hflip (u : ℝ) : |deriv (deriv F) u - deriv (deriv F) a| ≤ D * |u - a| := by
    rw [hF2, hF2]
    exact extendedCurvature_lipschitz hab hf'' hD u a
  have h := stationary_right_lipschitz_global hDn hℓ hab ((hFderiv a haa).trans ha)
    (fun u => (hFd u).differentiableAt) hFdd hFL hflip
  have hFe (u : ℝ) (hu : u ∈ Set.Icc a b) : F u = f u := extendedPhase_eq hab haa hu hf hf' hfc
  have he : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((F u - ν * u : ℝ) : ℂ))) =
      ∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact congrArg (fun v : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((v - ν * u : ℝ) : ℂ))) (hFe u hu)
  rw [he, hFe a haa, hF2, extendedCurvature_eq hab haa, hFderiv b hbb] at h
  exact h


/-- The finite endpoint cap depends only on the absolute derivative gap. -/
theorem stationaryEndpointCap_neg (ℓ gap : ℝ) : stationaryEndpointCap ℓ (-gap) = stationaryEndpointCap ℓ gap := by
  simp only [stationaryEndpointCap, neg_eq_zero, abs_neg]

/-- Reflection supplies the left-hand half of the source nonlinear estimate. -/
theorem stationary_left_phase_bound {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hb : deriv f b = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) b| : ℂ) / 2‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f a - ν) := by
  let g : ℝ → ℝ := fun u => f (-u)
  have hmap {u : ℝ} (hu : u ∈ Set.Icc (-b) (-a)) : -u ∈ Set.Icc a b := by
    constructor <;> linarith [hu.1, hu.2]
  have hg : deriv g = fun u => -deriv f (-u) := funext (fun u => deriv_comp_neg f u)
  have hg2 : deriv (deriv g) = fun u => deriv (deriv f) (-u) := by
    funext u
    rw [hg]
    change deriv (-(fun v : ℝ => deriv f (-v))) u = deriv (deriv f) (-u)
    rw [deriv.neg, deriv_comp_neg, neg_neg]
  have hgd (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) : DifferentiableAt ℝ g u :=
    (hf (-u) (hmap hu)).comp u (hasDerivAt_neg u).differentiableAt
  have hgd' (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) : DifferentiableAt ℝ (deriv g) u := by
    rw [hg]
    exact ((hf' (-u) (hmap hu)).comp u (hasDerivAt_neg u).differentiableAt).neg
  have hgd'' (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (deriv (deriv g)) (-deriv (deriv (deriv f)) (-u)) u := by
    rw [hg2]
    convert (hf'' (-u) (hmap hu)).hasDerivAt.comp u (hasDerivAt_neg u) using 1
    ring
  have h := stationary_right_phase_bound (ν := -ν) hℓ (by linarith : -b ≤ -a)
    (by rw [hg]; simp only [neg_neg, hb]) hgd hgd'
    (fun u hu => (hgd'' u hu).differentiableAt)
    (fun u hu => by rw [hg2]; exact hcurv (-u) (hmap hu))
    (fun u hu => by rw [(hgd'' u hu).deriv, abs_neg]; exact hD (-u) (hmap hu))
  have he (u : ℝ) : g u - (-ν) * u = f (-u) - ν * (-u) := by dsimp [g]; ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_comp_neg
    (fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)))] at h
  rw [hg2, hg] at h
  simp only [neg_neg] at h
  rw [show -deriv f a - -ν = -(deriv f a - ν) by ring, stationaryEndpointCap_neg] at h
  exact h



end DhimanKadiriQuesadaHerrera2026
