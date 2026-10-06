import DhimanKadiriQuesadaHerrera2026.StationaryWindow

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory Filter

/-- Integrating a pointwise derivative power bound gives its exact factorial-free primitive bound. -/
theorem sub_bound_of_deriv_power {g : ℝ → ℝ} {c x D : ℝ} (n : ℕ)
    (hd : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ g u)
    (hb : ∀ u ∈ Set.uIcc c x, |deriv g u| ≤ D * |u - c| ^ n) :
    |g x - g c| ≤ D * |x - c| ^ (n + 1) / (n + 1) := by
  have hB : IntervalIntegrable (fun u : ℝ => D * |u - c| ^ n) volume c x :=
    (continuous_const.mul ((continuous_id.sub continuous_const).abs.pow n)).intervalIntegrable _ _
  have hae : ∀ᵐ u ∂volume.restrict (Set.uIoc c x), ‖deriv g u‖ ≤ D * |u - c| ^ n := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    exact hb u (Set.uIoc_subset_uIcc hu)
  have hdi : IntervalIntegrable (deriv g) volume c x :=
    hB.mono_fun' (aestronglyMeasurable_deriv g _) hae
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => (hd u hu).hasDerivAt) hdi
  rw [← he, ← Real.norm_eq_abs, intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  apply (MeasureTheory.norm_integral_le_of_norm_le hB.def' hae).trans_eq
  rw [MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
  ring

/-- Lipschitz curvature supplies the exact quadratic first-derivative remainder without a third derivative. -/
theorem derivative_taylor_remainder_lipschitz {f : ℝ → ℝ} {c x D : ℝ}
    (hf' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.uIcc c x, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    |deriv f x - deriv f c - (x - c) * deriv (deriv f) c| ≤ D * |x - c| ^ 2 / 2 := by
  let q : ℝ → ℝ := fun u => deriv f u - deriv f c - (u - c) * deriv (deriv f) c
  have hq (u : ℝ) (hu : u ∈ Set.uIcc c x) :
      HasDerivAt q (deriv (deriv f) u - deriv (deriv f) c) u := by
    simpa only [one_mul] using ((hf' u hu).hasDerivAt.sub_const (deriv f c)).sub
      (((hasDerivAt_id u).sub_const c).mul_const (deriv (deriv f) c))
  have h := sub_bound_of_deriv_power 1 (fun u hu => (hq u hu).differentiableAt)
    (D := D) (fun u hu => by rw [(hq u hu).deriv, pow_one]; exact hL u hu)
  simpa only [q, sub_self, zero_mul, sub_zero, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using h

/-- The cubic phase remainder follows from Lipschitz curvature and two ordinary derivatives. -/
theorem quadratic_taylor_remainder_lipschitz {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.uIcc c x, DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.uIcc c x, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    |f x - f c - (x - c) * deriv f c - (x - c) ^ 2 * deriv (deriv f) c / 2| ≤
      D * |x - c| ^ 3 / 6 := by
  let q : ℝ → ℝ := fun u => f u - f c - (u - c) * deriv f c - (u - c) ^ 2 * deriv (deriv f) c / 2
  have hq (u : ℝ) (hu : u ∈ Set.uIcc c x) :
      HasDerivAt q (deriv f u - deriv f c - (u - c) * deriv (deriv f) c) u := by
    have h := (((hf u hu).hasDerivAt.sub_const (f c)).sub
      (((hasDerivAt_id u).sub_const c).mul_const (deriv f c))).sub
      (((((hasDerivAt_id u).sub_const c).pow 2).mul_const (deriv (deriv f) c)).div_const 2)
    convert h using 1
    simp only [id_eq]
    ring
  have hbound (u : ℝ) (hu : u ∈ Set.uIcc c x) :
      |deriv q u| ≤ (D / 2) * |u - c| ^ 2 := by
    have hs : Set.uIcc c u ⊆ Set.uIcc c x := Set.uIcc_subset_uIcc (Set.left_mem_uIcc) hu
    rw [(hq u hu).deriv]
    apply (derivative_taylor_remainder_lipschitz (fun v hv => hf' v (hs hv))
      (fun v hv => hL v (hs hv))).trans_eq
    ring
  have h := sub_bound_of_deriv_power 2 (fun u hu => (hq u hu).differentiableAt) hbound
  simp only [q, sub_self, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    Nat.reduceAdd, Nat.cast_ofNat] at h
  exact h.trans_eq (by ring)

/-- The genuine centered error satisfies both Taylor bounds using Lipschitz curvature alone. -/
theorem stationaryTaylorError_bounds_lipschitz {f : ℝ → ℝ} {c x D : ℝ}
    (hf : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.uIcc c (c + x), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    |stationaryTaylorError f c x| ≤ D * |x| ^ 3 / 6 ∧
      |deriv (stationaryTaylorError f c) x| ≤ D * |x| ^ 2 / 2 := by
  constructor
  · simpa only [stationaryTaylorError, add_sub_cancel_left] using quadratic_taylor_remainder_lipschitz hf hf' hL
  · rw [(stationaryTaylorError_hasDerivAt (hf (c + x) Set.right_mem_uIcc)).deriv]
    simpa only [add_sub_cancel_left] using derivative_taylor_remainder_lipschitz hf' hL

/-- The nonlinear integral bound extends to twice differentiable phases with Lipschitz curvature. -/
theorem stationary_taylor_integral_lipschitz {f : ℝ → ℝ} {c δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖∫ x in (-δ)..δ,
      Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) - 1)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| := by
  have hm (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) : Set.uIcc c (c + x) ⊆ Set.Icc (c - δ) (c + δ) :=
    Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hb (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) := stationaryTaylorError_bounds_lipschitz
    (fun u hu => hf u (hm x hx hu)) (fun u hu => hf' u (hm x hx hu)) (fun u hu => hL u (hm x hx hu))
  exact stationary_perturbation_integral_bound hκ hδ
    (fun x hx => (stationaryTaylorError_hasDerivAt (hf (c + x) (hm x hx Set.right_mem_uIcc))).differentiableAt)
    (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)

/-- The actual shifted phase can be replaced on its central window by its quadratic phase with the source nonlinear error. -/
theorem stationary_centered_window_lipschitz {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ x in (-δ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
        ∫ x in (-δ)..δ,
          Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| := by
  let C : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ))
  let Q : ℝ → ℂ := fun x => Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2)
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hCn : ‖C‖ = 1 := by
    dsimp [C]
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hfactor (x : ℝ) :
      Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)) =
        C * Q x * Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) := by
    have h := stationary_phase_factorization hc x
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ) =
        Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2 := by
      push_cast
      ring
    rw [he] at h
    exact h
  have hfc : ContinuousOn f (Set.Icc (c - δ) (c + δ)) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hfx : ContinuousOn (fun x => f (c + x)) (Set.Icc (-δ) δ) := by
    apply hfc.comp (continuous_const.add continuous_id).continuousOn
    intro x hx
    change c + x ∈ Set.Icc (c - δ) (c + δ)
    constructor <;> linarith [hx.1, hx.2]
  have hei : IntervalIntegrable
      (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)))
      volume (-δ) δ := by
    have hh : ContinuousOn
        (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)))
        (Set.Icc (-δ) δ) := by
      have hp : ContinuousOn (fun x : ℝ => f (c + x) - ν * (c + x)) (Set.Icc (-δ) δ) :=
        hfx.sub ((continuous_const.add continuous_id).continuousOn.const_mul ν)
      exact Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hp).const_mul (2 * Real.pi * Complex.I))
    exact hh.intervalIntegrable_of_Icc (by linarith)
  have hid : (∫ x in (-δ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      C * (∫ x in (-δ)..δ, Q x) =
      C * (∫ x in (-δ)..δ, Q x *
        (Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) - 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hei ((hQ.const_mul C).intervalIntegrable _ _),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [Pi.sub_apply]
    rw [hfactor]
    ring
  change ‖(∫ x in (-δ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      C * (∫ x in (-δ)..δ, Q x)‖ ≤ _
  rw [hid, norm_mul, hCn, one_mul]
  exact stationary_taylor_integral_lipschitz hδ hκ hf hf' hL

/-- The actual central stationary integral has the evaluated main term and both exact errors. -/
theorem stationary_central_fresnel_lipschitz {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c < 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in (c - δ)..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| + 1 / (Real.pi * |deriv (deriv f) c| * δ) := by
  have h1 := stationary_centered_window_lipschitz hδ hκ.ne hc hf hf' hL
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

/-- A genuine central window contained in the source interval gives the full nonlinear stationary estimate. -/
theorem stationary_lipschitz_interval_window {f : ℝ → ℝ} {a b c ν δ D ℓ : ℝ}
    (hDn : 0 ≤ D) (hδ : 0 < δ) (hℓ : 0 < ℓ) (ha : a ≤ c - δ) (hb : c + δ ≤ b)
    (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hL : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
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
  have hLeftBound := norm_shifted_integral_positive ha (fun u hu => hf u (hleft hu))
    (hfc.mono hleft) (hm.mono hleft) (by nlinarith [mul_pos hℓ hδ] : ν < deriv f (c - δ))
  have hR := norm_shifted_integral_negative hb (fun u hu => hf u (hright hu))
    (hfc.mono hright) (hm.mono hright) (by nlinarith [mul_pos hℓ hδ] : deriv f (c + δ) < ν)
  have hLL : ‖∫ u in a..(c - δ), Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * ℓ * δ) := hLeftBound.trans (by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hl Real.pi_pos.le])
  have hRR : ‖∫ u in (c + δ)..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      1 / (Real.pi * ℓ * δ) := hR.trans (by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hr Real.pi_pos.le])
  have hC := stationary_central_fresnel_lipschitz hδ hκ hc (fun u hu => hf u (hmid hu))
    (fun u hu => hf' u (hmid hu)) (fun u hu => hL u (hmid hu))
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

end DhimanKadiriQuesadaHerrera2026
