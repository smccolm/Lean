import DhimanKadiriQuesadaHerrera2026.StationaryPerturb
import DhimanKadiriQuesadaHerrera2026.FresnelSharp

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The actual central stationary integral has the evaluated main term and both exact errors. -/
theorem stationary_central_fresnel_bound {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c < 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in (c - δ)..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| + 1 / (Real.pi * |deriv (deriv f) c| * δ) := by
  have h1 := stationary_centered_window_bound hδ hκ.ne hc hf hf' hf'' hD
  have h2 := quadratic_stationary_phase_sharp (f c - ν * c) hκ hδ
  have hi : (∫ x in (-δ)..δ,
      Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) =
      ∫ u in (c - δ)..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    simpa only [sub_eq_add_neg] using intervalIntegral.integral_comp_add_left
      (fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) c
      (a := -δ) (b := δ)
  rw [hi] at h1
  have hq : (∫ x in (-δ)..δ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f c - ν * c + deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
        ∫ x in (-δ)..δ,
          Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hq] at h2
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h1 h2)

/-- A curvature lower bound controls the actual drop of the first derivative. -/
theorem stationary_derivative_drop {f : ℝ → ℝ} {a b ℓ x y : ℝ}
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hℓ : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    ℓ * (y - x) ≤ deriv f x - deriv f y := by
  have hh := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun u hu => (hf' u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hf' u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hℓ u (interior_subset hu)) x hx y hy hxy
  linarith

/-- The positive-slope side of the actual shifted phase has its reciprocal endpoint estimate. -/
theorem norm_shifted_integral_positive {f : ℝ → ℝ} {a b ν : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : AntitoneOn (deriv f) (Set.Icc a b)) (hb : ν < deriv f b) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * (deriv f b - ν)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < deriv f u - ν := by
    have hh := hm hu (Set.right_mem_Icc.mpr hab.le) hu.2
    linarith
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun u => 2 * Real.pi * (f u - ν * u))
        (2 * Real.pi * (deriv f u - ν)) u := by
    simpa only [id_eq, mul_one] using
      ((hf u hu).hasDerivAt.sub ((hasDerivAt_id u).const_mul ν)).const_mul (2 * Real.pi)
  have hq (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |1 / (2 * Real.pi * (deriv f u - ν))| = 1 / (2 * Real.pi * (deriv f u - ν)) :=
    abs_of_pos (by have hh := hp u hu; positivity)
  have hh := first_derivative_test_monotone hab hd ((hfc.sub continuousOn_const).const_mul _)
    (g := fun _ => 1) continuousOn_const
    (fun u hu => by have hp' := hp u hu; positivity)
    (by
      intro x hx y hy hxy
      dsimp only
      rw [hq x hx, hq y hy]
      exact one_div_le_one_div_of_le (by have hh := hp y hy; positivity)
        (mul_le_mul_of_nonneg_left (sub_le_sub_right (hm hx hy hxy) ν) Real.two_pi_pos.le))
  simp only [Complex.ofReal_one, one_mul, hq b (Set.right_mem_Icc.mpr hab.le)] at hh
  have he (u : ℝ) : Complex.I * ((2 * Real.pi * (f u - ν * u) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ) := by push_cast; ring
  simp_rw [he] at hh
  apply hh.trans_eq
  field_simp

/-- The negative-slope side of the actual shifted phase has its reciprocal endpoint estimate. -/
theorem norm_shifted_integral_negative {f : ℝ → ℝ} {a b ν : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : AntitoneOn (deriv f) (Set.Icc a b)) (ha : deriv f a < ν) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * (ν - deriv f a)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv f u < ν :=
    (hm (Set.left_mem_Icc.mpr hab.le) hu hu.1).trans_lt ha
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun u => 2 * Real.pi * (f u - ν * u))
        (2 * Real.pi * (deriv f u - ν)) u := by
    simpa only [id_eq, mul_one] using
      ((hf u hu).hasDerivAt.sub ((hasDerivAt_id u).const_mul ν)).const_mul (2 * Real.pi)
  have hq (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |1 / (2 * Real.pi * (deriv f u - ν))| = 1 / (2 * Real.pi * (ν - deriv f u)) := by
    rw [abs_div, abs_one, abs_of_neg (by have hh := hp u hu; nlinarith [Real.pi_pos])]
    congr 1
    ring
  have hh := first_derivative_test_antitone hab hd ((hfc.sub continuousOn_const).const_mul _)
    (g := fun _ => 1) continuousOn_const
    (fun u hu => mul_ne_zero Real.two_pi_pos.ne' (sub_ne_zero.mpr (hp u hu).ne))
    (by
      intro x hx y hy hxy
      dsimp only
      rw [hq x hx, hq y hy]
      exact one_div_le_one_div_of_le (by have hh := hp x hx; positivity)
        (mul_le_mul_of_nonneg_left (sub_le_sub_left (hm hx hy hxy) ν) Real.two_pi_pos.le))
  simp only [Complex.ofReal_one, one_mul, hq a (Set.left_mem_Icc.mpr hab.le)] at hh
  have he (u : ℝ) : Complex.I * ((2 * Real.pi * (f u - ν * u) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ) := by push_cast; ring
  simp_rw [he] at hh
  apply hh.trans_eq
  field_simp

/-- A genuine central window contained in the source interval gives the full nonlinear stationary estimate. -/
theorem stationary_interval_bound_of_window {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a ≤ c - δ) (hb : c + δ ≤ b)
    (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) := by
  have hac : a ≤ c := by linarith
  have hcb : c ≤ b := by linarith
  have hcc : c ∈ Set.Icc a b := ⟨hac, hcb⟩
  have hcm : c - δ ∈ Set.Icc a b := ⟨ha, by linarith⟩
  have hcp : c + δ ∈ Set.Icc a b := ⟨by linarith, hb⟩
  have hκ : deriv (deriv f) c < 0 := (hcurv c hcc).trans_lt (neg_neg_of_pos hℓ)
  have hk : ℓ ≤ |deriv (deriv f) c| := by rw [abs_of_neg hκ]; linarith [hcurv c hcc]
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD c hcc)
  have hm : AntitoneOn (deriv f) (Set.Icc a b) := by
    intro x hx y hy hxy
    have hh := stationary_derivative_drop hf' hcurv hx hy hxy
    have hp := mul_nonneg hℓ.le (sub_nonneg.mpr hxy)
    linarith
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hl : ℓ * δ ≤ deriv f (c - δ) - ν := by
    have h := stationary_derivative_drop hf' hcurv hcm hcc (by linarith)
    rw [hc] at h
    convert h using 1
    ring
  have hr : ℓ * δ ≤ ν - deriv f (c + δ) := by
    have h := stationary_derivative_drop hf' hcurv hcc hcp (by linarith)
    rw [hc] at h
    convert h using 1
    ring
  have hleft : Set.Icc a (c - δ) ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hcm.2
  have hright : Set.Icc (c + δ) b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left hcp.1
  have hmid : Set.Icc (c - δ) (c + δ) ⊆ Set.Icc a b := Set.Icc_subset_Icc ha hb
  have hL := norm_shifted_integral_positive ha (fun u hu => hf u (hleft hu))
    (hfc.mono hleft) (hm.mono hleft) (by nlinarith [mul_pos hℓ hδ] : ν < deriv f (c - δ))
  have hR := norm_shifted_integral_negative hb (fun u hu => hf u (hright hu))
    (hfc.mono hright) (hm.mono hright) (by nlinarith [mul_pos hℓ hδ] : deriv f (c + δ) < ν)
  have hLL : ‖∫ u in a..(c - δ), Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * ℓ * δ) := hL.trans (by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hl Real.pi_pos.le])
  have hRR : ‖∫ u in (c + δ)..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * ℓ * δ) := hR.trans (by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hr Real.pi_pos.le])
  have hC := stationary_central_fresnel_bound hδ hκ hc (fun u hu => hf u (hmid hu))
    (fun u hu => hf' u (hmid hu)) (fun u hu => hf'' u (hmid hu)) (fun u hu => hD u (hmid hu))
  have hCC : ‖(∫ u in (c - δ)..(c + δ),
      Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / ℓ + 1 / (Real.pi * ℓ * δ) := hC.trans (add_le_add
        (div_le_div_of_nonneg_left (by positivity) hℓ hk)
        (one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk Real.pi_pos.le) hδ.le)))
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  have hK : ContinuousOn K (Set.Icc a b) := by
    have hfu : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    exact Complex.continuous_exp.comp_continuousOn ((Complex.continuous_ofReal.comp_continuousOn
      (hfu.sub (continuous_const.mul continuous_id).continuousOn)).const_mul (2 * Real.pi * Complex.I))
  have hKi {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) (huv : u ≤ v) :
      IntervalIntegrable K volume u v := (hK.mono (Set.Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  have hsplit : (∫ u in a..b, K u) = (∫ u in a..(c - δ), K u) +
      (∫ u in (c - δ)..(c + δ), K u) + (∫ u in (c + δ)..b, K u) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hKi le_rfl hcm.2 ha)
      (hKi ha hb (by linarith : c - δ ≤ c + δ))
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hKi le_rfl hb (by linarith : a ≤ c + δ))
      (hKi hcp.1 le_rfl hb)
    linear_combination -h1 -h2
  let M : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv f) c| : ℂ)
  change ‖(∫ u in a..b, K u) - M‖ ≤ _
  rw [hsplit]
  have he : (∫ u in a..(c - δ), K u) + (∫ u in (c - δ)..(c + δ), K u) +
      (∫ u in (c + δ)..b, K u) - M =
      ((∫ u in a..(c - δ), K u) + ((∫ u in (c - δ)..(c + δ), K u) - M)) +
        (∫ u in (c + δ)..b, K u) := by ring
  rw [he]
  apply (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  exact (add_le_add (add_le_add hLL hCC) hRR).trans_eq (by ring)

/-- The source radius balances the two rigorous stationary errors with the exact real-power coefficient. -/
theorem stationary_radius_error_eq {D ℓ : ℝ} (hD : 0 < D) (hℓ : 0 < ℓ) :
    let δ := (3 / (Real.pi * D)) ^ (1 / 3 : ℝ)
    D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) =
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ := by
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
  change D * δ ^ 2 / ℓ + 3 / (Real.pi * ℓ * δ) = _
  rw [hbalance, hmain]
  ring

/-- When the source radius fits inside the interval, the actual integral satisfies the exact nonlinear coefficient. -/
theorem stationary_interval_source_constant_of_window {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hD : 0 < D) (hℓ : 0 < ℓ)
    (ha : a ≤ c - (3 / (Real.pi * D)) ^ (1 / 3 : ℝ))
    (hb : c + (3 / (Real.pi * D)) ^ (1 / 3 : ℝ) ≤ b)
    (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hthird : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ := by
  have hδ : 0 < (3 / (Real.pi * D)) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  exact (stationary_interval_bound_of_window hδ hℓ ha hb hc hf hf' hf'' hcurv hthird).trans_eq
    (stationary_radius_error_eq hD hℓ)

end DhimanKadiriQuesadaHerrera2026


