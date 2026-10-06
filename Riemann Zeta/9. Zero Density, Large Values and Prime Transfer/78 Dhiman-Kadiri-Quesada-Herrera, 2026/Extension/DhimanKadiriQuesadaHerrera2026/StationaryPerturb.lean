import DhimanKadiriQuesadaHerrera2026.StationaryTaylor
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace DhimanKadiriQuesadaHerrera2026
open Filter MeasureTheory
open scoped Topology

/-- The genuine amplitude used to integrate the quadratic perturbation by parts away from zero. -/
noncomputable def stationaryPerturbation (g : ℝ → ℝ) (κ x : ℝ) : ℂ :=
  (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1) /
    (2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ))

/-- Exact size of the nonzero quadratic integration-by-parts denominator. -/
theorem norm_stationary_denominator (κ x : ℝ) :
    ‖2 * (Real.pi : ℂ) * Complex.I * (κ : ℂ) * (x : ℂ)‖ = 2 * Real.pi * |κ| * |x| := by
  simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The cubic Taylor error makes the apparent singular boundary amplitude quadratic at zero. -/
theorem stationaryPerturbation_bound {g : ℝ → ℝ} {κ x D : ℝ}
    (hκ : κ ≠ 0) (hx : x ≠ 0) (hg : |g x| ≤ D * |x| ^ 3 / 6) :
    ‖stationaryPerturbation g κ x‖ ≤ D * |x| ^ 2 / (6 * |κ|) := by
  rw [stationaryPerturbation, norm_div, norm_stationary_denominator]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * |κ| * |x|)).mpr
  have h := (norm_exp_two_pi_sub_one_le (g x)).trans
    (mul_le_mul_of_nonneg_left hg Real.two_pi_pos.le)
  apply h.trans_eq
  field_simp

/-- Differentiating the actual complex perturbation retains both derivative and reciprocal terms. -/
theorem stationaryPerturbation_hasDerivAt {g : ℝ → ℝ} {κ x : ℝ}
    (hκ : κ ≠ 0) (hx : x ≠ 0) (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (stationaryPerturbation g κ)
      ((((deriv g x : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ))) /
        ((κ : ℂ) * (x : ℂ)) -
      (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1) /
        (2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2)) x := by
  have he := ((hg.hasDerivAt.ofReal_comp.const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp).sub_const 1
  have hd := (hasDerivAt_id x).ofReal_comp.const_mul (2 * (Real.pi : ℂ) * Complex.I * (κ : ℂ))
  have hn : 2 * (Real.pi : ℂ) * Complex.I * (κ : ℂ) * (x : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hκ)) (Complex.ofReal_ne_zero.mpr hx)
  have h := he.div hd hn
  convert h using 1
  simp only [id_eq, Complex.ofReal_one]
  have hκ' := Complex.ofReal_ne_zero.mpr hκ
  have hx' := Complex.ofReal_ne_zero.mpr hx
  field_simp

/-- Both Taylor bounds give the exact integrable linear bound on the perturbation derivative. -/
theorem stationaryPerturbation_deriv_bound {g : ℝ → ℝ} {κ x D : ℝ}
    (hκ : κ ≠ 0) (hx : x ≠ 0) (hd : DifferentiableAt ℝ g x)
    (hg : |g x| ≤ D * |x| ^ 3 / 6) (hg' : |deriv g x| ≤ D * |x| ^ 2 / 2) :
    ‖deriv (stationaryPerturbation g κ) x‖ ≤ 2 * D * |x| / (3 * |κ|) := by
  have hn : ‖Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have h1 : ‖(((deriv g x : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ))) /
      ((κ : ℂ) * (x : ℂ))‖ ≤ D * |x| / (2 * |κ|) := by
    rw [norm_div, norm_mul, hn, mul_one, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (by positivity : 0 < |κ| * |x|)).mpr
    apply hg'.trans_eq
    field_simp
  have h2 : ‖(Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1) /
      (2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2)‖ ≤ D * |x| / (6 * |κ|) := by
    rw [norm_div]
    have he : ‖2 * (Real.pi : ℂ) * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2‖ =
        2 * Real.pi * |κ| * |x| ^ 2 := by
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * |κ| * |x| ^ 2)).mpr
    apply ((norm_exp_two_pi_sub_one_le (g x)).trans
      (mul_le_mul_of_nonneg_left hg Real.two_pi_pos.le)).trans_eq
    field_simp
  rw [(stationaryPerturbation_hasDerivAt hκ hx hd).deriv]
  exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- The actual centered phase supplies both integration-by-parts amplitude bounds. -/
theorem stationaryTaylorPerturbation_bounds {f : ℝ → ℝ} {c x D : ℝ}
    (hx : x ≠ 0) (hκ : deriv (deriv f) c ≠ 0)
    (hf : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.uIcc c (c + x), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.uIcc c (c + x), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖stationaryPerturbation (stationaryTaylorError f c) (deriv (deriv f) c) x‖ ≤
      D * |x| ^ 2 / (6 * |deriv (deriv f) c|) ∧
    ‖deriv (stationaryPerturbation (stationaryTaylorError f c) (deriv (deriv f) c)) x‖ ≤
      2 * D * |x| / (3 * |deriv (deriv f) c|) := by
  have hd := hf (c + x) Set.right_mem_uIcc
  have h1 := stationaryTaylorError_bound hf hf' hf'' hD
  have h2 := stationaryTaylorError_deriv_bound hd hf' hf'' hD
  exact ⟨stationaryPerturbation_bound hκ hx h1,
    stationaryPerturbation_deriv_bound hκ hx (stationaryTaylorError_hasDerivAt hd).differentiableAt h1 h2⟩

/-- The cubic error removes the apparent pole and gives derivative zero at the center. -/
theorem stationaryPerturbation_hasDerivAt_zero {g : ℝ → ℝ} {κ D : ℝ} (hκ : κ ≠ 0)
    (hg : ∀ᶠ x in 𝓝 (0 : ℝ), |g x| ≤ D * |x| ^ 3 / 6) :
    HasDerivAt (stationaryPerturbation g κ) 0 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hz : stationaryPerturbation g κ 0 = 0 := by simp [stationaryPerturbation]
  have ht : Tendsto (fun x : ℝ => D * |x| / (6 * |κ|)) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => D * |x| / (6 * |κ|)) 0 := by fun_prop
    simpa only [abs_zero, mul_zero, zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' ?_ ht
  filter_upwards [hg.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hx0
  have hxn : x ≠ 0 := hx0
  simp only [zero_add, hz, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv]
  apply (mul_le_mul_of_nonneg_left (stationaryPerturbation_bound hκ hxn hx) (inv_nonneg.mpr (abs_nonneg x))).trans_eq
  field_simp

/-- The absolute first moment of a symmetric interval is exactly its squared radius. -/
theorem integral_abs_symmetric {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ x in (-δ)..δ, |x|) = δ ^ 2 := by
  have hn : (∫ x in (-δ)..0, |x|) = ∫ x in (-δ)..0, -x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -δ ≤ (0 : ℝ))] at hx
    exact abs_of_nonpos hx.2
  have hp : (∫ x in (0 : ℝ)..δ, |x|) = ∫ x in (0 : ℝ)..δ, x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hδ] at hx
    exact abs_of_nonneg hx.1
  rw [← intervalIntegral.integral_add_adjacent_intervals (continuous_abs.intervalIntegrable _ _) (continuous_abs.intervalIntegrable _ _),
    hn, hp, intervalIntegral.integral_neg, integral_id, integral_id]
  ring

/-- Integration by parts controls the actual nonlinear perturbation with its full quadratic radius error. -/
theorem stationary_perturbation_integral_bound {g : ℝ → ℝ} {κ δ D : ℝ}
    (hκ : κ ≠ 0) (hδ : 0 < δ)
    (hd : ∀ x ∈ Set.Icc (-δ) δ, DifferentiableAt ℝ g x)
    (hg : ∀ x ∈ Set.Icc (-δ) δ, |g x| ≤ D * |x| ^ 3 / 6)
    (hg' : ∀ x ∈ Set.Icc (-δ) δ, |deriv g x| ≤ D * |x| ^ 2 / 2) :
    ‖∫ x in (-δ)..δ,
      Complex.exp (Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1)‖ ≤ D * δ ^ 2 / |κ| := by
  let A := stationaryPerturbation g κ
  let Q : ℝ → ℂ := fun x => Complex.exp (Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2)
  have hab : -δ ≤ δ := by linarith
  have hzero : HasDerivAt A 0 0 := stationaryPerturbation_hasDerivAt_zero hκ (by
    filter_upwards [Icc_mem_nhds (by linarith : -δ < (0 : ℝ)) hδ] with x hx
    exact hg x hx)
  have hA (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) : HasDerivAt A (deriv A x) x := by
    by_cases hx0 : x = 0
    · subst x
      rw [hzero.deriv]
      exact hzero
    · exact (stationaryPerturbation_hasDerivAt hκ hx0 (hd x hx)).differentiableAt.hasDerivAt
  have hAb (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) : ‖deriv A x‖ ≤ 2 * D * |x| / (3 * |κ|) := by
    by_cases hx0 : x = 0
    · subst x
      simp [hzero.deriv]
    · exact stationaryPerturbation_deriv_bound hκ hx0 (hd x hx) (hg x hx) (hg' x hx)
  have hAc : IntervalIntegrable (deriv A) volume (-δ) δ := by
    have hi : IntervalIntegrable (fun x : ℝ => 2 * D * |x| / (3 * |κ|)) volume (-δ) δ :=
      ((continuous_const.mul continuous_abs).div_const _).intervalIntegrable _ _
    apply hi.mono_fun' (aestronglyMeasurable_deriv A _)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Set.uIoc_of_le hab] at hx
    exact hAb x ⟨hx.1.le, hx.2⟩
  have hQ (x : ℝ) : HasDerivAt Q (2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x) x := by
    have h := (((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (Real.pi * Complex.I * (κ : ℂ))).cexp
    convert h using 1
    dsimp [Q]
    ring
  have hQn (x : ℝ) : ‖Q x‖ = 1 := by
    dsimp [Q]
    have he : (Real.pi : ℂ) * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2 =
        ((Real.pi * κ * x ^ 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  have hQc : IntervalIntegrable (fun x => 2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x) volume (-δ) δ := by
    have hc : Continuous (fun (x : ℝ) => 2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x) := by
      dsimp [Q]
      fun_prop
    exact hc.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hA x (Set.uIcc_of_le hab ▸ hx)) (fun x _ => hQ x) hAc hQc
  have hg0 : g 0 = 0 := by
    have hh := hg 0 ⟨by linarith, hδ.le⟩
    simpa using hh
  have he : (∫ x in (-δ)..δ, A x * (2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x)) =
      ∫ x in (-δ)..δ, Q x * (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1) := by
    apply intervalIntegral.integral_congr
    intro x _
    by_cases hx0 : x = 0
    · subst x
      simp [hg0]
    · dsimp only [A, stationaryPerturbation]
      have hκ' := Complex.ofReal_ne_zero.mpr hκ
      have hx' := Complex.ofReal_ne_zero.mpr hx0
      field_simp
  rw [he] at hparts
  have hi : ‖∫ x in (-δ)..δ, deriv A x * Q x‖ ≤ 2 * D * δ ^ 2 / (3 * |κ|) := by
    have hb : ‖∫ x in (-δ)..δ, deriv A x * Q x‖ ≤ ∫ x in (-δ)..δ, 2 * D * |x| / (3 * |κ|) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall (fun x hx => ?_))
        (((continuous_const.mul continuous_abs).div_const _).intervalIntegrable _ _)
      rw [norm_mul, hQn, mul_one]
      exact hAb x ⟨hx.1.le, hx.2⟩
    simpa only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_abs_symmetric hδ.le] using hb
  have hpa := stationaryPerturbation_bound hκ (neg_ne_zero.mpr hδ.ne') (hg (-δ) ⟨le_rfl, hab⟩)
  have hpb := stationaryPerturbation_bound hκ hδ.ne' (hg δ ⟨hab, le_rfl⟩)
  rw [hparts]
  have ht := (norm_sub_le (A δ * Q δ - A (-δ) * Q (-δ)) (∫ x in (-δ)..δ, deriv A x * Q x)).trans
    (add_le_add (norm_sub_le _ _) le_rfl)
  simp only [norm_mul, hQn, mul_one] at ht
  simp only [abs_neg, abs_of_pos hδ] at hpa hpb
  apply ht.trans
  change ‖stationaryPerturbation g κ δ‖ + ‖stationaryPerturbation g κ (-δ)‖ +
    ‖∫ x in (-δ)..δ, deriv A x * Q x‖ ≤ _
  apply (add_le_add (add_le_add hpb hpa) hi).trans_eq
  ring

/-- The actual centered Taylor error satisfies the complete nonlinear integral bound on its genuine window. -/
theorem stationary_taylor_integral_bound {f : ℝ → ℝ} {c δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv (deriv f)) u| ≤ D) :
    ‖∫ x in (-δ)..δ,
      Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) - 1)‖ ≤
      D * δ ^ 2 / |deriv (deriv f) c| := by
  have hm (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) : Set.uIcc c (c + x) ⊆ Set.Icc (c - δ) (c + δ) := by
    intro u hu
    rcases le_total 0 x with hx0 | hx0
    · rw [Set.uIcc_of_le (by linarith : c ≤ c + x)] at hu
      constructor <;> linarith [hu.1, hu.2, hx.1, hx.2]
    · rw [Set.uIcc_of_ge (by linarith : c + x ≤ c)] at hu
      constructor <;> linarith [hu.1, hu.2, hx.1, hx.2]
  apply stationary_perturbation_integral_bound hκ hδ
  · intro x hx
    exact (stationaryTaylorError_hasDerivAt (hf (c + x) (hm x hx Set.right_mem_uIcc))).differentiableAt
  · intro x hx
    exact stationaryTaylorError_bound (fun u hu => hf u (hm x hx hu))
      (fun u hu => hf' u (hm x hx hu)) (fun u hu => hf'' u (hm x hx hu)) (fun u hu => hD u (hm x hx hu))
  · intro x hx
    exact stationaryTaylorError_deriv_bound (hf (c + x) (hm x hx Set.right_mem_uIcc))
      (fun u hu => hf' u (hm x hx hu)) (fun u hu => hf'' u (hm x hx hu)) (fun u hu => hD u (hm x hx hu))

/-- The actual shifted phase can be replaced on its central window by its quadratic phase with the source nonlinear error. -/
theorem stationary_centered_window_bound {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv (deriv f)) u| ≤ D) :
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
  exact stationary_taylor_integral_bound hδ hκ hf hf' hf'' hD

end DhimanKadiriQuesadaHerrera2026
