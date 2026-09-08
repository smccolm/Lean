import GafniTao.FordKFiniteRectangle
import PrimeNumberTheoremAnd.LaplaceInversion

/-!
# The inverse-Laplace term in Ford's `K(s)` argument

This file isolates the exact change of variables in Ford's `J_n` integral.
The integration variable on the zeta line is converted to the inverse
bilateral-Laplace line through `v = Im(s) - u`; no contour limit or source
function is hidden in the notation.
-/

open Complex Set Filter MeasureTheory FourierTransform
open scoped FourierTransform Topology

namespace GafniTao

noncomputable section

/-- Ford's finite-height `J` integral, with `x = log n` in the source
application. -/
noncomputable def fordJTrunc
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha R x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ u in (-R)..R,
      Complex.exp (-((alpha : ℂ) + (u : ℂ) * I) * (x : ℂ)) *
        F₀ (s - ((alpha : ℂ) + (u : ℂ) * I))

/-- The shifted finite inverse-Laplace integral occurring after the literal
substitution `v = Im(s) - u`. -/
noncomputable def fordShiftedLaplaceInvTrunc
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha R x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ v in (s.im - R)..(s.im + R),
      Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        F₀ (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I)

private theorem fordLaplace_shift_point (s : ℂ) (alpha u : ℝ) :
    (((s.re - alpha : ℝ) : ℂ) + ((s.im - u : ℝ) : ℂ) * I) =
      s - ((alpha : ℂ) + (u : ℂ) * I) := by
  apply Complex.ext
  · simp
  · simp

/-- Exact finite-height change of variables in Ford's `J_n`. -/
theorem fordJTrunc_eq_exp_neg_mul_shiftedLaplace
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha R x : ℝ) :
    fordJTrunc F₀ s alpha R x =
      Complex.exp (-s * (x : ℂ)) *
        fordShiftedLaplaceInvTrunc F₀ s alpha R x := by
  unfold fordJTrunc fordShiftedLaplaceInvTrunc
  let q : ℝ → ℂ := fun v =>
    Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
      F₀ (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I)
  have hpoint : ∀ u : ℝ,
      Complex.exp (-((alpha : ℂ) + (u : ℂ) * I) * (x : ℂ)) *
          F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)) =
        Complex.exp (-s * (x : ℂ)) * q (s.im - u) := by
    intro u
    have hshift := fordLaplace_shift_point s alpha u
    dsimp [q]
    rw [hshift]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  have hchange :
      (∫ u in (-R)..R, q (s.im - u)) =
        ∫ v in (s.im - R)..(s.im + R), q v := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := -R) (b := R) q s.im
    simp only [sub_neg_eq_add] at h
    exact h
  rw [hchange]
  dsimp [q]
  ring

/-- On a positive real base, Ford's exponential notation is the literal
complex power `n^{-w}` used in the paper. -/
theorem ford_exp_neg_mul_log_eq_cpow_neg
    {x : ℝ} (hx : 0 < x) (w : ℂ) :
    Complex.exp (-w * (Real.log x : ℂ)) = (x : ℂ) ^ (-w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

/-- Source-form specialization of the finite `J_n` integral for positive
natural `n`. -/
theorem fordJTrunc_log_nat_eq_cpow
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha R : ℝ) {n : ℕ} (hn : 0 < n) :
    fordJTrunc F₀ s alpha R (Real.log n) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ u in (-R)..R,
          ((n : ℂ) ^ (-((alpha : ℂ) + (u : ℂ) * I))) *
            F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)) := by
  unfold fordJTrunc
  congr 1
  apply intervalIntegral.integral_congr
  intro u _hu
  change Complex.exp (-((alpha : ℂ) + (u : ℂ) * I) *
      (Real.log (n : ℝ) : ℂ)) * F₀ (s - ((alpha : ℂ) + (u : ℂ) * I)) = _
  rw [ford_exp_neg_mul_log_eq_cpow_neg (by exact_mod_cast hn)]
  rfl

/-- A general finite inverse-Laplace window.  Ford's shifted window and the
standard symmetric Bromwich window are instances of this definition. -/
noncomputable def fordLaplaceInvWindow
    (F : ℂ → ℂ) (sigma a b x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ v in a..b,
      Complex.exp (((sigma : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        F ((sigma : ℂ) + (v : ℂ) * I)

/-- The absolutely convergent full inverse-Laplace line. -/
noncomputable def fordLaplaceInvFull
    (F : ℂ → ℂ) (sigma x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ v : ℝ,
      Complex.exp (((sigma : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        F ((sigma : ℂ) + (v : ℂ) * I)

/-- The source shifted integral is a `fordLaplaceInvWindow` with its literal
endpoints. -/
theorem fordShiftedLaplaceInvTrunc_eq_window
    (F₀ : ℂ → ℂ) (s : ℂ) (alpha R x : ℝ) :
    fordShiftedLaplaceInvTrunc F₀ s alpha R x =
      fordLaplaceInvWindow F₀ (s.re - alpha) (s.im - R) (s.im + R) x := by
  rfl

/-- The complex multiplication normalization agrees with the vector-valued
normalization in the pinned bilateral-Laplace library. -/
theorem fordLaplaceInvWindow_symmetric_eq_laplaceInvLineTrunc
    (F : ℂ → ℂ) (sigma x R : ℝ) :
    fordLaplaceInvWindow F sigma (-R) R x =
      laplaceInvLineTrunc sigma F x R := by
  unfold fordLaplaceInvWindow laplaceInvLineTrunc
  simp only [smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  rfl

/-- Any fixed translate of an absolutely integrable inverse-Laplace line
converges to the same full line integral. -/
theorem tendsto_fordLaplaceInvWindow_center
    {F : ℂ → ℂ} {sigma center x : ℝ}
    (hline : Integrable (fun v : ℝ =>
      Complex.exp (((sigma : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        F ((sigma : ℂ) + (v : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      fordLaplaceInvWindow F sigma (center - R) (center + R) x)
      atTop (𝓝 (fordLaplaceInvFull F sigma x)) := by
  have hleft : Tendsto (fun R : ℝ => center - R) atTop atBot := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atBot_add_const_left atTop center tendsto_neg_atTop_atBot)
  have hright : Tendsto (fun R : ℝ => center + R) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop center tendsto_id
  have hint := intervalIntegral_tendsto_integral hline hleft hright
  unfold fordLaplaceInvWindow fordLaplaceInvFull
  exact hint.const_mul (1 / (2 * (Real.pi : ℂ)))

/-- The full absolutely convergent Bromwich line recovers a source value.
The local quotient is the standard pointwise Fourier-inversion hypothesis;
it is not a Ford zero-free or density assumption. -/
theorem fordLaplaceInvFull_laplaceTransform_eq
    {g : ℝ → ℂ} {sigma x radius : ℝ}
    (hradius : 0 < radius)
    (hg : Integrable (fun y : ℝ =>
      Complex.exp (-((sigma : ℂ) * (y : ℂ))) * g y))
    (hquot : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (Complex.exp (-((sigma : ℂ) * ((x - u : ℝ) : ℂ))) * g (x - u) -
              Complex.exp (-((sigma : ℂ) * (x : ℂ))) * g x))
      volume (-radius) radius)
    (hline : Integrable (fun v : ℝ =>
      Complex.exp (((sigma : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral g ((sigma : ℂ) + (v : ℂ) * I))) :
    fordLaplaceInvFull (laplaceTransformBilateral g) sigma x = g x := by
  have hsinc := sinc_kernel_tendsto_of_integrable_local_quotient
    (E := ℂ)
    (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * g y)
    (x := x) (R := radius) hg hradius hquot
  have hfourier := fourierInvTrunc_tendsto_of_sinc_kernel
    (E := ℂ)
    (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * g y)
    hg hsinc
  have hinv := laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (E := ℂ) sigma g (x := x) hfourier
  have hfull := tendsto_fordLaplaceInvWindow_center
    (F := laplaceTransformBilateral g) (sigma := sigma)
    (center := 0) (x := x) hline
  have hfull' : Tendsto
      (fun R : ℝ => laplaceInvLineTrunc sigma (laplaceTransformBilateral g) x R)
      atTop (𝓝 (fordLaplaceInvFull (laplaceTransformBilateral g) sigma x)) := by
    refine hfull.congr' ?_
    filter_upwards with R
    rw [zero_sub, zero_add,
      fordLaplaceInvWindow_symmetric_eq_laplaceInvLineTrunc]
  exact tendsto_nhds_unique hfull' hinv

/-- Ford's literal shifted inverse-Laplace window recovers the same source
value, with no unrecorded recentering error. -/
theorem tendsto_fordShiftedLaplaceInvTrunc
    {g : ℝ → ℂ} {s : ℂ} {alpha x radius : ℝ}
    (hradius : 0 < radius)
    (hg : Integrable (fun y : ℝ =>
      Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) * g y))
    (hquot : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * ((x - u : ℝ) : ℂ))) *
                g (x - u) -
              Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (x : ℂ))) * g x))
      volume (-radius) radius)
    (hline : Integrable (fun v : ℝ =>
      Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral g
          (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      fordShiftedLaplaceInvTrunc (laplaceTransformBilateral g) s alpha R x)
      atTop (𝓝 (g x)) := by
  rw [show g x = fordLaplaceInvFull (laplaceTransformBilateral g)
      (s.re - alpha) x by
    symm
    exact fordLaplaceInvFull_laplaceTransform_eq
      hradius hg hquot hline]
  simpa only [fordShiftedLaplaceInvTrunc_eq_window] using
    (tendsto_fordLaplaceInvWindow_center
      (F := laplaceTransformBilateral g) (sigma := s.re - alpha)
      (center := s.im) (x := x) hline)

private theorem ford_laplace_weight_differentiable
    {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (sigma : ℝ) :
    Differentiable ℝ
      (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * g y) := by
  intro y
  have hofReal : DifferentiableAt ℝ (fun z : ℝ => (z : ℂ)) y :=
    Complex.ofRealCLM.differentiable.differentiableAt
  have hlin : DifferentiableAt ℝ
      (fun z : ℝ => -((sigma : ℂ) * (z : ℂ))) y := by
    simpa only [neg_mul] using hofReal.const_mul (-(sigma : ℂ))
  exact hlin.cexp.mul ((hg.differentiable (by norm_num)).differentiableAt)

/-- Local continuity and differentiability at the recovery point are enough
to discharge the Fourier quotient in the shifted Bromwich formula.  This is
the form used at the positive points `x = log n` in Ford's proof. -/
theorem tendsto_fordShiftedLaplaceInvTrunc_of_local_regular
    {g : ℝ → ℂ} {s : ℂ} {alpha x radius : ℝ}
    (hradius : 0 < radius)
    (hgcont : ContinuousOn g (Set.Icc (x - radius) (x + radius)))
    (hgdiff : DifferentiableAt ℝ g x)
    (hg : Integrable (fun y : ℝ =>
      Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) * g y))
    (hline : Integrable (fun v : ℝ =>
      Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral g
          (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      fordShiftedLaplaceInvTrunc (laplaceTransformBilateral g) s alpha R x)
      atTop (𝓝 (g x)) := by
  let q : ℝ → ℂ := fun y =>
    Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) * g y
  have hqcont : ContinuousOn q (Set.Icc (x - radius) (x + radius)) := by
    dsimp [q]
    exact (Complex.continuous_exp.comp (by continuity)).continuousOn.mul hgcont
  have hofReal : DifferentiableAt ℝ (fun y : ℝ => (y : ℂ)) x :=
    Complex.ofRealCLM.differentiable.differentiableAt
  have hlin : DifferentiableAt ℝ
      (fun y : ℝ => -(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) x := by
    simpa only [neg_mul] using
      hofReal.const_mul (-((s.re - alpha : ℝ) : ℂ))
  have hqdiff : DifferentiableAt ℝ q x := by
    exact hlin.cexp.mul hgdiff
  have hquot : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) •
            (Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * ((x - u : ℝ) : ℂ))) *
                g (x - u) -
              Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (x : ℂ))) * g x))
      volume (-radius) radius := by
    simpa only [q] using
      intervalIntegrable_local_quotient_of_differentiableAt
        (E := ℂ) (f := q) (x := x) hradius hqcont hqdiff
  exact tendsto_fordShiftedLaplaceInvTrunc hradius hg hquot hline

/-- A `C¹` source automatically supplies the local Fourier-inversion
quotient in Ford's shifted Bromwich formula.  Only the two global
integrability obligations remain explicit. -/
theorem tendsto_fordShiftedLaplaceInvTrunc_of_contDiff
    {g : ℝ → ℂ} {s : ℂ} {alpha x : ℝ}
    (hgdiff : ContDiff ℝ 1 g)
    (hg : Integrable (fun y : ℝ =>
      Complex.exp (-(((s.re - alpha : ℝ) : ℂ) * (y : ℂ))) * g y))
    (hline : Integrable (fun v : ℝ =>
      Complex.exp ((((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I) * (x : ℂ)) *
        laplaceTransformBilateral g
          (((s.re - alpha : ℝ) : ℂ) + (v : ℂ) * I))) :
    Tendsto (fun R : ℝ =>
      fordShiftedLaplaceInvTrunc (laplaceTransformBilateral g) s alpha R x)
      atTop (𝓝 (g x)) := by
  exact tendsto_fordShiftedLaplaceInvTrunc_of_local_regular
    (radius := 1) (by norm_num) hgdiff.continuous.continuousOn
    ((hgdiff.differentiable (by norm_num)).differentiableAt) hg hline

end

end GafniTao
