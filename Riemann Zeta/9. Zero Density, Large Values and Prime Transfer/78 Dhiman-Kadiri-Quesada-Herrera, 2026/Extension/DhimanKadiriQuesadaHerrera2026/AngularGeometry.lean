import DhimanKadiriQuesadaHerrera2026.KershnerBound

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- An increasing positive angular derivative bounds the actual complex tail by twice its initial reciprocal. -/
theorem norm_angular_positive_tail {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : MonotoneOn (deriv f) (Set.Icc a b)) (hp : 0 < deriv f a) :
    ‖∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)‖ ≤ 2 / deriv f a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  have hpos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < deriv f u :=
    hp.trans_le (hm (Set.left_mem_Icc.mpr hab.le) hu hu.1)
  have h := first_derivative_test_antitone hab (fun u hu => (hf u hu).hasDerivAt) hfc
    (g := fun _ => 1) continuousOn_const (fun u hu => (hpos u hu).ne') (by
      intro x hx y hy hxy
      dsimp only
      have hxpos := hpos x hx
      have hypos := hpos y hy
      rw [abs_of_pos (by positivity : 0 < 1 / deriv f x), abs_of_pos (by positivity : 0 < 1 / deriv f y)]
      exact one_div_le_one_div_of_le (hpos x hx) (hm hx hy hxy))
  simp only [Complex.ofReal_one, one_mul, abs_of_pos (by positivity : 0 < 1 / deriv f a)] at h
  simp_rw [mul_comm Complex.I] at h
  exact h.trans_eq (by ring)

/-- A nonnegative cosine prefix dominates its exact primitive divided by the terminal slope. -/
theorem cosine_prefix_lower {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : MonotoneOn (deriv f) (Set.Icc a b)) (hp : 0 < deriv f b)
    (hcos : ∀ u ∈ Set.Icc a b, 0 ≤ Real.cos (f u)) :
    (Real.sin (f b) - Real.sin (f a)) / deriv f b ≤ ∫ u in a..b, Real.cos (f u) := by
  have hc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hcc : ContinuousOn (fun u => Real.cos (f u)) (Set.Icc a b) := Real.continuous_cos.comp_continuousOn hc
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun u => Real.sin (f u)) (Real.cos (f u) * deriv f u) u := (hf u hu).hasDerivAt.sin
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (by simpa only [Set.uIcc_of_le hab] using hu))
    ((hcc.mul hfc).intervalIntegrable_of_Icc (μ := volume) hab)
  have hi : (∫ u in a..b, Real.cos (f u) * deriv f u) ≤
      ∫ u in a..b, Real.cos (f u) * deriv f b := by
    apply intervalIntegral.integral_mono_on hab
      ((hcc.mul hfc).intervalIntegrable_of_Icc (μ := volume) hab)
      ((hcc.mul_const _).intervalIntegrable_of_Icc hab)
    intro u hu
    exact mul_le_mul_of_nonneg_left (hm hu (Set.right_mem_Icc.mpr hab) hu.2) (hcos u hu)
  rw [he, intervalIntegral.integral_mul_const] at hi
  exact (div_le_iff₀ hp).mpr hi

/-- A nonnegative sine prefix has the corresponding exact primitive lower bound. -/
theorem sine_prefix_lower {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hm : MonotoneOn (deriv f) (Set.Icc a b)) (hp : 0 < deriv f b)
    (hsin : ∀ u ∈ Set.Icc a b, 0 ≤ Real.sin (f u)) :
    (Real.cos (f a) - Real.cos (f b)) / deriv f b ≤ ∫ u in a..b, Real.sin (f u) := by
  let g : ℝ → ℝ := fun u => f u - Real.pi / 2
  have hg : deriv g = deriv f := deriv_sub_const_fun _
  have hgd (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ g u := (hf u hu).sub_const _
  have h := cosine_prefix_lower (f := g) hab hgd (by rw [hg]; exact hfc)
    (by rw [hg]; exact hm) (by rw [hg]; exact hp) (by
      intro u hu
      simpa only [g, Real.cos_sub_pi_div_two] using hsin u hu)
  simpa only [g, hg, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, sub_neg_eq_add, neg_add_eq_sub] using h

/-- Starting at zero phase, an increasing nonnegative derivative gives a nonnegative sine integral. -/
theorem sine_curvature_nonneg {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) (ha : f a = 0) :
    0 ≤ ∫ u in a..b, Real.sin (f u) := by
  have hc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    (fun u hu => (hf u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hpos u (interior_subset hu))
  have hm' := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc'
    (fun u hu => (hf' u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hℓ.le.trans (hcurv u (interior_subset hu)))
  have hfa (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 ≤ f u := by
    rw [← ha]
    exact hm (Set.left_mem_Icc.mpr hab) hu hu.1
  by_cases hb : f b ≤ Real.pi
  · apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact Real.sin_nonneg_of_nonneg_of_le_pi (hfa u hu)
      ((hm hu (Set.right_mem_Icc.mpr hab) hu.2).trans hb)
  obtain ⟨c, hcc, he⟩ := intermediate_value_Icc hab hc ⟨by rw [ha]; exact Real.pi_pos.le, (le_of_not_ge hb)⟩
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcc.2
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc hcc.1 le_rfl
  have hv : 0 < deriv f c := by
    have hh := curvature_energy_lower hf hf' hpos hcurv hcc
    rw [ha, he] at hh
    have hp := hpos c hcc
    nlinarith [mul_pos hℓ Real.pi_pos, sq_nonneg (deriv f a)]
  have hp := sine_prefix_lower hcc.1 (fun u hu => hf u (hleft hu)) (hc'.mono hleft) (hm'.mono hleft) hv
    (fun u hu => Real.sin_nonneg_of_nonneg_of_le_pi (hfa u (hleft hu))
      ((hm (hleft hu) hcc hu.2).trans_eq he))
  rw [ha, he, Real.cos_zero, Real.cos_pi] at hp
  norm_num only [sub_neg_eq_add, one_add_one_eq_two] at hp
  have ht := norm_angular_positive_tail hcc.2 (fun u hu => hf u (hright hu))
    (hc'.mono hright) (hm'.mono hright) hv
  have hk : ContinuousOn (fun u => Complex.exp ((f u : ℂ) * Complex.I)) (Set.Icc a b) := by fun_prop
  have him := intervalIntegral.intervalIntegral_im ((hk.mono hright).intervalIntegrable_of_Icc (μ := volume) hcc.2)
  simp only [RCLike.im_eq_complex_im, Complex.exp_ofReal_mul_I_im] at him
  have ht' : -(2 / deriv f c) ≤ ∫ u in c..b, Real.sin (f u) := by
    rw [him]
    have hh := neg_le_of_abs_le (Complex.abs_im_le_norm (∫ u in c..b, Complex.exp ((f u : ℂ) * Complex.I)))
    linarith
  have hs : ContinuousOn (fun u => Real.sin (f u)) (Set.Icc a b) := Real.continuous_sin.comp_continuousOn hc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hs.mono hleft).intervalIntegrable_of_Icc (μ := volume) hcc.1)
    ((hs.mono hright).intervalIntegrable_of_Icc (μ := volume) hcc.2)]
  linarith

/-- The positive initial cosine prefix halves the naive negative real-part tail bound. -/
theorem cosine_curvature_lower {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) (ha : f a = 0) :
    -(1 / Real.sqrt (Real.pi * ℓ)) ≤ ∫ u in a..b, Real.cos (f u) := by
  have hc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hc' : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    (fun u hu => (hf u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hpos u (interior_subset hu))
  have hm' := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc'
    (fun u hu => (hf' u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hℓ.le.trans (hcurv u (interior_subset hu)))
  have hfa (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 ≤ f u := by
    rw [← ha]
    exact hm (Set.left_mem_Icc.mpr hab) hu hu.1
  by_cases hb : f b ≤ Real.pi / 2
  · apply (neg_nonpos.mpr (by positivity) : -(1 / Real.sqrt (Real.pi * ℓ)) ≤ 0).trans
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hfa u hu, Real.pi_pos],
      (hm hu (Set.right_mem_Icc.mpr hab) hu.2).trans hb⟩
  obtain ⟨c, hcc, he⟩ := intermediate_value_Icc hab hc
    ⟨by rw [ha]; positivity, (le_of_not_ge hb)⟩
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcc.2
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc hcc.1 le_rfl
  have henergy := curvature_energy_lower hf hf' hpos hcurv hcc
  rw [ha, he] at henergy
  have hv : 0 < deriv f c := by
    have hp := hpos c hcc
    nlinarith [mul_pos hℓ Real.pi_pos, sq_nonneg (deriv f a)]
  have hroot : Real.sqrt (Real.pi * ℓ) ≤ deriv f c := by
    nlinarith [Real.sq_sqrt (mul_nonneg Real.pi_pos.le hℓ.le), Real.sqrt_nonneg (Real.pi * ℓ), sq_nonneg (deriv f a)]
  have hp := cosine_prefix_lower hcc.1 (fun u hu => hf u (hleft hu)) (hc'.mono hleft) (hm'.mono hleft) hv
    (fun u hu => Real.cos_nonneg_of_mem_Icc ⟨by linarith [hfa u (hleft hu), Real.pi_pos],
      (hm (hleft hu) hcc hu.2).trans_eq he⟩)
  rw [ha, he, Real.sin_zero, Real.sin_pi_div_two, sub_zero] at hp
  have ht := norm_angular_positive_tail hcc.2 (fun u hu => hf u (hright hu))
    (hc'.mono hright) (hm'.mono hright) hv
  have hk : ContinuousOn (fun u => Complex.exp ((f u : ℂ) * Complex.I)) (Set.Icc a b) := by fun_prop
  have hre := intervalIntegral.intervalIntegral_re ((hk.mono hright).intervalIntegrable_of_Icc (μ := volume) hcc.2)
  simp only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] at hre
  have ht' : -(2 / deriv f c) ≤ ∫ u in c..b, Real.cos (f u) := by
    rw [hre]
    have hh := neg_le_of_abs_le (Complex.abs_re_le_norm (∫ u in c..b, Complex.exp ((f u : ℂ) * Complex.I)))
    linarith
  have hs : ContinuousOn (fun u => Real.cos (f u)) (Set.Icc a b) := Real.continuous_cos.comp_continuousOn hc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hs.mono hleft).intervalIntegrable_of_Icc (μ := volume) hcc.1)
    ((hs.mono hright).intervalIntegrable_of_Icc (μ := volume) hcc.2)]
  have hr := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hℓ)) hroot
  rw [show 2 / deriv f c = 2 * (1 / deriv f c) by ring] at ht'
  linarith

/-- A geometric enclosure controls distance to every admissible half stationary main term. -/
theorem norm_sub_quarter_main {z : ℂ} {A : ℝ} (hA : 0 ≤ A) (hAmax : A ≤ 1 / 2)
    (hz : ‖z‖ ≤ 0.6715) (hre : -(1 / (Real.pi * Real.sqrt 2)) ≤ z.re) (him : 0 ≤ z.im) :
    ‖z - (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤ 0.928 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrexp : (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)).re = Real.sqrt 2 / 2 := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four]
  have himexp : (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)).im = Real.sqrt 2 / 2 := by
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_four]
  have he : ‖z - (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      ‖z‖ ^ 2 + A ^ 2 - A * Real.sqrt 2 * (z.re + z.im) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
      hrexp, himexp]
    nlinarith [mul_self_nonneg (A * Real.sqrt 2), hs2]
  have hcross : -(A * Real.sqrt 2 * (z.re + z.im)) ≤ A / Real.pi := by
    have h := mul_le_mul_of_nonneg_left (show -(z.re + z.im) ≤ 1 / (Real.pi * Real.sqrt 2) by linarith)
      (mul_nonneg hA hs.le)
    have heq : A * Real.sqrt 2 * (1 / (Real.pi * Real.sqrt 2)) = A / Real.pi := by field_simp
    rw [heq] at h
    nlinarith
  have hAdiv : A / Real.pi ≤ 1 / (2 * Real.pi) := by
    convert div_le_div_of_nonneg_right hAmax Real.pi_pos.le using 1
    ring
  have hpi : 1 / (2 * Real.pi) ≤ 1 / (2 * 3.14) := one_div_le_one_div_of_le (by norm_num)
    (by linarith [Real.pi_gt_d4])
  have hAsq := mul_self_le_mul_self hA hAmax
  have hzsq := mul_self_le_mul_self (norm_nonneg z) hz
  nlinarith [norm_nonneg (z - (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))]

/-- The actual one-sided integral is within 0.928 of every admissible half stationary amplitude, at the curvature scale. -/
theorem norm_positive_half_sub_main {f : ℝ → ℝ} {a b ℓ A : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, 2 * Real.pi * ℓ ≤ deriv (deriv f) u) (ha : f a = 0)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (2 * Real.sqrt ℓ)) :
    ‖(∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)) -
      (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ ≤ 0.928 / Real.sqrt ℓ := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  let z : ℂ := (Real.sqrt ℓ : ℂ) * ∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)
  have hn := norm_curvature_positive_slope hab (mul_pos Real.two_pi_pos hℓ) hf hf' hpos hcurv
  rw [show 2 * Real.pi * ℓ / 2 = Real.pi * ℓ by ring, Real.sqrt_mul Real.pi_pos.le] at hn
  have hzn : ‖z‖ ≤ 0.6715 := by
    simp only [z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    apply (mul_le_mul_of_nonneg_left hn hs.le).trans
    have he : Real.sqrt ℓ * (119 / (100 * (Real.sqrt Real.pi * Real.sqrt ℓ))) = 119 / (100 * Real.sqrt Real.pi) := by field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 100 * Real.sqrt Real.pi)).mpr
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.pi_gt_d4]
  have hkc : ContinuousOn (fun u => Complex.exp ((f u : ℂ) * Complex.I)) (Set.Icc a b) := by
    have hc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    fun_prop
  have hr := intervalIntegral.intervalIntegral_re (hkc.intervalIntegrable_of_Icc (μ := volume) hab)
  have hi := intervalIntegral.intervalIntegral_im (hkc.intervalIntegrable_of_Icc (μ := volume) hab)
  simp only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] at hr
  simp only [RCLike.im_eq_complex_im, Complex.exp_ofReal_mul_I_im] at hi
  have him : 0 ≤ z.im := by
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← hi]
    exact mul_nonneg hs.le (sine_curvature_nonneg hab (mul_pos Real.two_pi_pos hℓ) hf hf' hpos hcurv ha)
  have hsqrt : Real.sqrt (Real.pi * (2 * Real.pi * ℓ)) = Real.pi * Real.sqrt 2 * Real.sqrt ℓ := by
    rw [show Real.pi * (2 * Real.pi * ℓ) = Real.pi ^ 2 * (2 * ℓ) by ring,
      Real.sqrt_mul (sq_nonneg Real.pi), Real.sqrt_sq_eq_abs, abs_of_pos Real.pi_pos,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hre : -(1 / (Real.pi * Real.sqrt 2)) ≤ z.re := by
    simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hr]
    have h := mul_le_mul_of_nonneg_left
      (cosine_curvature_lower hab (mul_pos Real.two_pi_pos hℓ) hf hf' hpos hcurv ha) hs.le
    have he : Real.sqrt ℓ * -(1 / Real.sqrt (Real.pi * (2 * Real.pi * ℓ))) =
        -(1 / (Real.pi * Real.sqrt 2)) := by rw [hsqrt]; field_simp
    rw [he] at h
    exact h
  have hA' : A * Real.sqrt ℓ ≤ 1 / 2 := by
    apply (le_div_iff₀ hs).mp
    convert hAmax using 1
    ring
  have h := norm_sub_quarter_main (mul_nonneg hA hs.le) hA' hzn hre him
  have he : z - ((A * Real.sqrt ℓ : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      (Real.sqrt ℓ : ℂ) * ((∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)) -
        (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) := by dsimp [z]; push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at h
  exact (le_div_iff₀ hs).mpr (by nlinarith)


end DhimanKadiriQuesadaHerrera2026
