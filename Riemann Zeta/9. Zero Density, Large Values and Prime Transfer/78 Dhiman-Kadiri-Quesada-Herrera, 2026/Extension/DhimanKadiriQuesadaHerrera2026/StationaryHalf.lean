import DhimanKadiriQuesadaHerrera2026.StationaryFullSum

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- Integration by parts controls the actual nonlinear perturbation with its full quadratic radius error. -/
theorem stationary_perturbation_half_bound {g : ℝ → ℝ} {κ δ D : ℝ}
    (hκ : κ ≠ 0) (hδ : 0 < δ)
    (hd : ∀ x ∈ Set.Icc (-δ) δ, DifferentiableAt ℝ g x)
    (hg : ∀ x ∈ Set.Icc (-δ) δ, |g x| ≤ D * |x| ^ 3 / 6)
    (hg' : ∀ x ∈ Set.Icc (-δ) δ, |deriv g x| ≤ D * |x| ^ 2 / 2) :
    ‖∫ x in (0 : ℝ)..δ,
      Complex.exp (Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1)‖ ≤ D * δ ^ 2 / (2 * |κ|) := by
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
  have hAc : IntervalIntegrable (deriv A) volume 0 δ := by
    have hi : IntervalIntegrable (fun x : ℝ => 2 * D * |x| / (3 * |κ|)) volume 0 δ :=
      ((continuous_const.mul continuous_abs).div_const _).intervalIntegrable _ _
    apply hi.mono_fun' (aestronglyMeasurable_deriv A _)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Set.uIoc_of_le hδ.le] at hx
    exact hAb x ⟨by linarith [hx.1], hx.2⟩
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
  have hQc : IntervalIntegrable (fun x => 2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x) volume 0 δ := by
    have hc : Continuous (fun (x : ℝ) => 2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x) := by
      dsimp [Q]
      fun_prop
    exact hc.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hA x (by rw [Set.uIcc_of_le hδ.le] at hx; exact ⟨by linarith [hx.1], hx.2⟩)) (fun x _ => hQ x) hAc hQc
  have hg0 : g 0 = 0 := by
    have hh := hg 0 ⟨by linarith, hδ.le⟩
    simpa using hh
  have he : (∫ x in (0 : ℝ)..δ, A x * (2 * Real.pi * Complex.I * (κ : ℂ) * (x : ℂ) * Q x)) =
      ∫ x in (0 : ℝ)..δ, Q x * (Complex.exp (2 * Real.pi * Complex.I * (g x : ℂ)) - 1) := by
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
  have hi : ‖∫ x in (0 : ℝ)..δ, deriv A x * Q x‖ ≤ D * δ ^ 2 / (3 * |κ|) := by
    have hb : ‖∫ x in (0 : ℝ)..δ, deriv A x * Q x‖ ≤ ∫ x in (0 : ℝ)..δ, 2 * D * |x| / (3 * |κ|) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hδ.le (Filter.Eventually.of_forall (fun x hx => ?_))
        (((continuous_const.mul continuous_abs).div_const _).intervalIntegrable _ _)
      rw [norm_mul, hQn, mul_one]
      exact hAb x ⟨by linarith [hx.1], hx.2⟩
    have hiAbs : (∫ x in (0 : ℝ)..δ, |x|) = δ ^ 2 / 2 := by
      calc
        _ = ∫ x in (0 : ℝ)..δ, x := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le hδ.le] at hx
          exact abs_of_nonneg hx.1
        _ = _ := by rw [integral_id]; ring
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, hiAbs] at hb
    exact hb.trans_eq (by ring)
  have hpb := stationaryPerturbation_bound hκ hδ.ne' (hg δ ⟨hab, le_rfl⟩)
  have hA0 : A 0 = 0 := by simp [A, stationaryPerturbation]
  rw [hparts, hA0, zero_mul, sub_zero]
  have ht := norm_sub_le (A δ * Q δ) (∫ x in (0 : ℝ)..δ, deriv A x * Q x)
  rw [norm_mul, hQn, mul_one] at ht
  simp only [abs_of_pos hδ] at hpb
  apply ht.trans
  exact (add_le_add hpb hi).trans_eq (by ring)

/-- The nonlinear integral bound extends to twice differentiable phases with Lipschitz curvature. -/
theorem stationary_taylor_half_lipschitz {f : ℝ → ℝ} {c δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖∫ x in (0 : ℝ)..δ,
      Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) - 1)‖ ≤
      D * δ ^ 2 / (2 * |deriv (deriv f) c|) := by
  have hm (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) : Set.uIcc c (c + x) ⊆ Set.Icc (c - δ) (c + δ) :=
    Set.uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hb (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) := stationaryTaylorError_bounds_lipschitz
    (fun u hu => hf u (hm x hx hu)) (fun u hu => hf' u (hm x hx hu)) (fun u hu => hL u (hm x hx hu))
  exact stationary_perturbation_half_bound hκ hδ
    (fun x hx => (stationaryTaylorError_hasDerivAt (hf (c + x) (hm x hx Set.right_mem_uIcc))).differentiableAt)
    (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)

/-- The actual shifted phase can be replaced on its central window by its quadratic phase with the source nonlinear error. -/
theorem stationary_centered_half_lipschitz {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c ≠ 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ x in (0 : ℝ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
        ∫ x in (0 : ℝ)..δ,
          Complex.exp (Real.pi * Complex.I * ((deriv (deriv f) c : ℝ) : ℂ) * (x : ℂ) ^ 2)‖ ≤
      D * δ ^ 2 / (2 * |deriv (deriv f) c|) := by
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
  have hfx : ContinuousOn (fun x => f (c + x)) (Set.Icc 0 δ) := by
    apply hfc.comp (continuous_const.add continuous_id).continuousOn
    intro x hx
    change c + x ∈ Set.Icc (c - δ) (c + δ)
    constructor <;> linarith [hx.1, hx.2]
  have hei : IntervalIntegrable
      (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)))
      volume 0 δ := by
    have hh : ContinuousOn
        (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ)))
        (Set.Icc 0 δ) := by
      have hp : ContinuousOn (fun x : ℝ => f (c + x) - ν * (c + x)) (Set.Icc 0 δ) :=
        hfx.sub ((continuous_const.add continuous_id).continuousOn.const_mul ν)
      exact Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hp).const_mul (2 * Real.pi * Complex.I))
    exact hh.intervalIntegrable_of_Icc (by linarith)
  have hid : (∫ x in (0 : ℝ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      C * (∫ x in (0 : ℝ)..δ, Q x) =
      C * (∫ x in (0 : ℝ)..δ, Q x *
        (Complex.exp (2 * Real.pi * Complex.I * (stationaryTaylorError f c x : ℂ)) - 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hei ((hQ.const_mul C).intervalIntegrable _ _),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [Pi.sub_apply]
    rw [hfactor]
    ring
  change ‖(∫ x in (0 : ℝ)..δ,
        Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) -
      C * (∫ x in (0 : ℝ)..δ, Q x)‖ ≤ _
  rw [hid, norm_mul, hCn, one_mul]
  exact stationary_taylor_half_lipschitz hδ hκ hf hf' hL

/-- The actual central stationary integral has the evaluated main term and both exact errors. -/
theorem stationary_half_fresnel_lipschitz {f : ℝ → ℝ} {c ν δ D : ℝ}
    (hδ : 0 < δ) (hκ : deriv (deriv f) c < 0) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc (c - δ) (c + δ), DifferentiableAt ℝ (deriv f) u)
    (hL : ∀ u ∈ Set.Icc (c - δ) (c + δ), |deriv (deriv f) u - deriv (deriv f) c| ≤ D * |u - c|) :
    ‖(∫ u in c..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ) / 2‖ ≤
      D * δ ^ 2 / (2 * |deriv (deriv f) c|) + 1 / (2 * Real.pi * |deriv (deriv f) c| * δ) := by
  have h1 := stationary_centered_half_lipschitz hδ hκ.ne hc hf hf' hL
  have h2 := quadratic_half_window_sharp (f c - ν * c) hκ hδ
  have hi : (∫ x in (0 : ℝ)..δ,
      Complex.exp (2 * Real.pi * Complex.I * ((f (c + x) - ν * (c + x) : ℝ) : ℂ))) =
      ∫ u in c..(c + δ),
        Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left
      (fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) c
      (a := 0) (b := δ)
  rw [hi] at h1
  have hq : (∫ x in (0 : ℝ)..δ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((f c - ν * c + deriv (deriv f) c * x ^ 2 / 2 : ℝ) : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c : ℝ) : ℂ)) *
        ∫ x in (0 : ℝ)..δ,
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



end DhimanKadiriQuesadaHerrera2026
