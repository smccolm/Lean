import DhimanKadiriQuesadaHerrera2026.PoissonCutoff

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- A four-fifths radius improves the nonlinear coefficient while keeping an exact rational calculation. -/
theorem stationary_radius_tight_eq {D ℓ : ℝ} (hD : 0 < D) (hℓ : 0 < ℓ) :
    let δ := (4 / 5 : ℝ) * (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) =
      (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ := by
  let δ := (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  have hcube : δ ^ 3 = 3 / (Real.pi * D) := by
    dsimp [δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 3 / (Real.pi * D))]
    norm_num
  have hsq : δ ^ 2 = (3 / (Real.pi * D)) ^ (2 / 3 : ℝ) := by
    dsimp [δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 3 / (Real.pi * D))]
    norm_num
  have hbalance : 3 / (Real.pi * ℓ * δ) = D * δ ^ 2 / ℓ := by
    have hh := (eq_div_iff (by positivity : Real.pi * D ≠ 0)).mp hcube
    apply (div_eq_iff (by positivity : Real.pi * ℓ * δ ≠ 0)).mpr
    field_simp
    nlinarith [hh]
  have hdp : D ^ (2 / 3 : ℝ) * D ^ (1 / 3 : ℝ) = D := by
    rw [← Real.rpow_add hD]
    norm_num
  have hdn : D ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hD _).ne'
  have hdiv : D / D ^ (2 / 3 : ℝ) = D ^ (1 / 3 : ℝ) := by
    apply (div_eq_iff hdn).mpr
    simpa only [mul_comm] using hdp.symm
  have hmain : D * δ ^ 2 = (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ) * D ^ (1 / 3 : ℝ) := by
    rw [hsq, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ Real.pi * D),
      Real.mul_rpow Real.pi_pos.le hD.le]
    calc
      _ = ((3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (D / D ^ (2 / 3 : ℝ)) := by ring
      _ = _ := by rw [hdiv]

  change D * ((4 / 5 : ℝ) * δ) ^ 2 / ℓ + 3 / (Real.pi * ℓ * ((4 / 5 : ℝ) * δ)) = _
  calc
    _ = (16 / 25 : ℝ) * (D * δ ^ 2 / ℓ) + (5 / 4 : ℝ) * (3 / (Real.pi * ℓ * δ)) := by ring
    _ = _ := by rw [hbalance, hmain]; ring


/-- The actual stationary integral admits the tighter 1.89 nonlinear coefficient and both finite endpoint caps. -/
theorem stationary_phase_gap_tight {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ +
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
  · let δ := (4 / 5 : ℝ) * (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    exact (stationary_interval_bound_gap hδ hℓ ha hb hc hf hf' hf'' hcurv hD).trans_eq
      (congrArg (fun z => z + stationaryEndpointCap ℓ (deriv f a - ν) + stationaryEndpointCap ℓ (deriv f b - ν)) (stationary_radius_tight_eq hpos hℓ))

/-- A smaller right-hand window gives half the tighter nonlinear coefficient, including zero variation. -/
theorem stationary_right_lipschitz_tight {f : ℝ → ℝ} {c b ν D ℓ : ℝ}
    (hDn : 0 ≤ D) (hℓ : 0 < ℓ) (hcb : c ≤ b) (hc : deriv f c = ν)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u, deriv (deriv f) u ≤ -ℓ)
    (hL : ∀ u, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in c..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
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
  · let δ := (4 / 5 : ℝ) * (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h := stationary_right_window_global hDn hδ hℓ hcb hc hf hf' hcurv hL
    apply h.trans_eq
    have he : D * δ ^ 2 / (2 * ℓ) + 3 / (2 * Real.pi * ℓ * δ) =
        ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 := by
      calc
        _ = (D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ)) / 2 := by ring
        _ = _ := congrArg (fun z => z / 2) (stationary_radius_tight_eq hpos hℓ)
    rw [he]

/-- The actual source phase supplies the tighter right-hand stationary estimate. -/
theorem stationary_right_phase_tight {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (ha : deriv f a = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) a| : ℂ) / 2‖ ≤
      ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
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
  have h := stationary_right_lipschitz_tight hDn hℓ hab ((hFderiv a haa).trans ha)
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

/-- Reflection supplies the tighter left-hand stationary estimate. -/
theorem stationary_left_phase_tight {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hb : deriv f b = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) b| : ℂ) / 2‖ ≤
      ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
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
  have h := stationary_right_phase_tight (ν := -ν) hℓ (by linarith : -b ≤ -a)
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

/-- A uniform left half combines with the tighter nonlinear right half and its far endpoint cap. -/
theorem stationary_error_drop_left_tight {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        0.928 / Real.sqrt ℓ + stationaryEndpointCap ℓ (deriv f b - ν) := by
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc ha le_rfl
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hl := stationary_left_half_uniform hℓ ha hc (fun u hu => hf u (hleft hu))
    (fun u hu => hf' u (hleft hu)) (hfc.mono hleft) (fun u hu => hcurv u (hleft hu))
  have hr := stationary_right_phase_tight hℓ hb hc (fun u hu => hf u (hright hu))
    (fun u hu => hf' u (hright hu)) (fun u hu => hf'' u (hright hu))
    (fun u hu => hcurv u (hright hu)) (fun u hu => hD u (hright hu))
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  let P : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
    (Real.sqrt |deriv (deriv f) c| : ℂ)
  have hK : ContinuousOn K (Set.Icc a b) := by
    have hcont : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    dsimp [K]
    fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((hK.mono hleft).intervalIntegrable_of_Icc (μ := volume) ha)
    ((hK.mono hright).intervalIntegrable_of_Icc (μ := volume) hb)
  have he : (∫ u in a..b, K u) - P =
      ((∫ u in a..c, K u) - P / 2) + ((∫ u in c..b, K u) - P / 2) := by rw [← hi]; ring
  change ‖(∫ u in a..b, K u) - P‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

/-- A uniform right half combines with the tighter nonlinear left half and its far endpoint cap. -/
theorem stationary_error_drop_right_tight {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        0.928 / Real.sqrt ℓ + stationaryEndpointCap ℓ (deriv f a - ν) := by
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc ha le_rfl
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hl := stationary_left_phase_tight hℓ ha hc (fun u hu => hf u (hleft hu))
    (fun u hu => hf' u (hleft hu)) (fun u hu => hf'' u (hleft hu))
    (fun u hu => hcurv u (hleft hu)) (fun u hu => hD u (hleft hu))
  have hr := stationary_right_half_uniform hℓ hb hc (fun u hu => hf u (hright hu))
    (fun u hu => hf' u (hright hu)) (hfc.mono hright) (fun u hu => hcurv u (hright hu))
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  let P : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
    (Real.sqrt |deriv (deriv f) c| : ℂ)
  have hK : ContinuousOn K (Set.Icc a b) := by
    have hcont : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    dsimp [K]
    fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((hK.mono hleft).intervalIntegrable_of_Icc (μ := volume) ha)
    ((hK.mono hright).intervalIntegrable_of_Icc (μ := volume) hb)
  have he : (∫ u in a..b, K u) - P =
      ((∫ u in a..c, K u) - P / 2) + ((∫ u in c..b, K u) - P / 2) := by rw [← hi]; ring
  change ‖(∫ u in a..b, K u) - P‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

/-- Every stationary main term is retained with the exact count of tighter nonlinear errors. -/
theorem stationary_full_sum_counted_tight {f : ℝ → ℝ} {a b D ℓ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        ((⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) *
          ((1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
  let M := ⌊deriv f a⌋₊
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P : ℕ → ℂ := fun ν => Complex.exp (2 * Real.pi * Complex.I *
    ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  let E : ℕ → ℂ := fun ν => I ν - P ν
  let A : ℕ → ℝ := fun ν => stationaryEndpointCap ℓ (deriv f a - (ν : ℝ))
  let B : ℕ → ℝ := fun ν => stationaryEndpointCap ℓ (deriv f b - (ν : ℝ))
  let r := (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  change 2 ≤ M at hM
  change ∀ ν ∈ Finset.Icc 1 M, _ at hξ
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hx1 := hξ 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hxM := hξ M (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have h1 : ‖E 1‖ ≤ r / 2 + 0.928 / Real.sqrt ℓ + A 1 :=
    stationary_error_drop_right_tight hℓ hx1.1.1 hx1.1.2 hx1.2 hf hf' hf'' hcurv hD
  have hlast : ‖E M‖ ≤ r / 2 + 0.928 / Real.sqrt ℓ + B M :=
    stationary_error_drop_left_tight hℓ hxM.1.1 hxM.1.2 hxM.2 hf hf' hf'' hcurv hD
  have hmid (ν : ℕ) (hν : ν ∈ Finset.Icc 2 (M - 1)) : ‖E ν‖ ≤ r + A ν + B ν := by
    have hn := Finset.mem_Icc.mp hν
    have hx := hξ ν (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact stationary_phase_gap_tight hℓ hx.1.1 hx.1.2 hx.2 hf hf' hf'' hcurv hD
  have hsum := norm_sum_stationary_edges hM E A B r (0.928 / Real.sqrt ℓ) h1 hlast hmid
  have hz : ‖I 0‖ ≤ 0.6715 / Real.sqrt ℓ := by
    simpa only [I, Nat.cast_zero, zero_mul, sub_zero] using
      kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos hlower
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hβα : deriv f b ≤ deriv f a := hanti.antitoneOn haa hbb hab.le
  have hβ : 0 ≤ deriv f a := hαpos.trans hβα
  have hfar := stationary_far_caps_sharp (ℓ := ℓ) hM hα (Nat.floor_le hβ)
  have hs : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have he : (∑ ν ∈ Finset.Icc 0 M, I ν) - (∑ ν ∈ Finset.Icc 1 M, P ν) =
      I 0 + ∑ ν ∈ Finset.Icc 1 M, E ν := by
    dsimp [E]
    rw [hs, Finset.sum_insert (by simp), Finset.sum_sub_distrib]
    ring
  change ‖(∑ ν ∈ Finset.Icc 0 M, I ν) - (∑ ν ∈ Finset.Icc 1 M, P ν)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans ((add_le_add hz hsum).trans ?_)
  have hconstant : 0.6715 / Real.sqrt ℓ + 2 * (0.928 / Real.sqrt ℓ) = 2.5275 / Real.sqrt ℓ := by ring
  change (∑ ν ∈ Finset.Icc 1 (M - 1), A ν) + (∑ ν ∈ Finset.Icc 2 M, B ν) ≤ _ at hfar
  dsimp only [M, r] at *
  norm_num only [div_eq_mul_inv] at hfar ⊢
  nlinarith only [hfar]

/-- The full stationary sum uses coefficient 1.89 in its source length-scaled nonlinear error. -/
theorem stationary_full_sum_sharp_tight {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
  have hs := stationary_full_sum_counted_tight ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hD
  let M := ⌊deriv f a⌋₊
  let r := (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hβα : deriv f b ≤ deriv f a := hanti.antitoneOn haa hbb hab.le
  have hcount := interior_frequency_card_le hα hβα
  have hcard : (Finset.Icc 1 (M - 1)).card = M - 1 := by rw [Nat.card_Icc]; omega
  change ((Finset.Icc 1 (M - 1)).card : ℝ) ≤ _ at hcount
  rw [hcard] at hcount
  have hw := derivative_range_le_curvature hab.le hf' hupper
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hscale : ((M - 1 : ℕ) : ℝ) * r ≤
      (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by
    apply (mul_le_mul_of_nonneg_right (hcount.trans hw) hr).trans_eq
    dsimp [r]
    field_simp
  exact hs.trans (add_le_add (add_le_add (add_le_add le_rfl hscale) le_rfl) le_rfl)

/-- The actual enlarged-cutoff discrete transform retains the tighter nonlinear coefficient and explicit Poisson error. -/
theorem exists_b_process_next_tight {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a))) +
      (1 / Real.pi) * (Real.log ((⌊deriv f a⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((⌊deriv f a⌋₊ : ℝ) + 1)) := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu (Set.right_mem_Icc.mpr hab.le) hu.2))
    hanti.antitoneOn
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  have hs := stationary_full_sum_sharp_tight ξ hab hℓ hαpos.le hα hM hξ hf hf' hf'' hanti hlower hupper hD
  have hp := poisson_next_cutoff_bound hr hℓ (Nat.lt_floor_add_one (deriv f a)) hf'
    (fun u hu => (hf'' u hu).continuousAt.continuousWithinAt) hcurv hah hbh
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simp only [sub_add_sub_cancel] at ht
  apply ht.trans_eq
  ring

end DhimanKadiriQuesadaHerrera2026
