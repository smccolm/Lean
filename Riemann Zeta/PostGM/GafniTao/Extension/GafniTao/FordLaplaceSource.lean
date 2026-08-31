import GafniTao.FordLaplaceInversion

/-!
# Ford's one-sided source and the exact `F₀` transform

Ford subtracts `f(0) / z` from the one-sided Laplace transform.  This file
models that subtraction as the bilateral Laplace transform of the literal
one-sided remainder `f(y) - f(0)`.  Thus the inverse transform used in
`J_n` recovers the source difference, rather than an abstract proxy.
-/

open Complex Set Filter MeasureTheory
open scoped Topology

namespace GafniTao

noncomputable section

/-- The one-sided complex Laplace transform in Ford's source. -/
noncomputable def fordLaplaceTransform (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ in Ioi 0,
    Complex.exp (-z * (y : ℂ)) * (f y : ℂ)

/-- Ford's pole-subtracted transform `F₀(z) = F(z) - f(0)/z`. -/
noncomputable def fordLaplaceF0 (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  fordLaplaceTransform f z - (f 0 : ℂ) / z

/-- Bilateral source whose transform is Ford's `F₀`.  The value at zero is
chosen as zero; this is the continuous value whenever `f` is continuous at
zero. -/
noncomputable def fordLaplaceRemainder (f : ℝ → ℝ) (y : ℝ) : ℂ :=
  if 0 < y then (f y - f 0 : ℝ) else 0

/-- The elementary complex exponential on a right half-plane is integrable
over Ford's positive ray. -/
theorem integrableOn_ford_complex_exponential
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-z * (y : ℂ))) (Ioi 0) := by
  simpa only [neg_mul] using
    (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa) 0)

/-- Exact integral of Ford's elementary pole term. -/
theorem integral_ford_complex_exponential
    {z : ℂ} (hz : 0 < z.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-z * (y : ℂ))) = 1 / z := by
  rw [show (fun y : ℝ => Complex.exp (-z * (y : ℂ))) =
    (fun y : ℝ => Complex.exp ((-z) * y)) by
    funext y
    rfl]
  rw [integral_exp_mul_complex_Ioi (a := -z) (by simpa) 0]
  simp only [ofReal_zero, mul_zero, exp_zero]
  field_simp [ne_of_gt hz]

/-- Absolute convergence of Ford's one-sided transform also gives the
weighted bilateral integrability of the pole-subtracted source. -/
theorem integrable_exp_mul_fordLaplaceRemainder
    {f : ℝ → ℝ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hf : IntegrableOn (fun y : ℝ =>
      Complex.exp (-((sigma : ℂ) * (y : ℂ))) * (f y : ℂ)) (Ioi 0)) :
    Integrable (fun y : ℝ =>
      Complex.exp (-((sigma : ℂ) * (y : ℂ))) *
        fordLaplaceRemainder f y) := by
  have hconst := integrableOn_ford_complex_exponential
    (z := (sigma : ℂ)) (by simpa)
  have hconstMul : IntegrableOn (fun y : ℝ =>
      Complex.exp (-((sigma : ℂ) * (y : ℂ))) * (f 0 : ℂ)) (Ioi 0) :=
    by simpa only [neg_mul] using hconst.mul_const (f 0 : ℂ)
  have hsub : IntegrableOn (fun y : ℝ =>
      Complex.exp (-((sigma : ℂ) * (y : ℂ))) *
        ((f y : ℂ) - (f 0 : ℂ))) (Ioi 0) := by
    simpa only [mul_sub] using hf.sub hconstMul
  have hindicator :
      (fun y : ℝ =>
        Complex.exp (-((sigma : ℂ) * (y : ℂ))) *
          fordLaplaceRemainder f y) =
        (Ioi (0 : ℝ)).indicator (fun y : ℝ =>
          Complex.exp (-((sigma : ℂ) * (y : ℂ))) *
            ((f y : ℂ) - (f 0 : ℂ))) := by
    funext y
    by_cases hy : 0 < y
    · simp [fordLaplaceRemainder, hy]
    · simp [fordLaplaceRemainder, hy]
  rw [hindicator]
  exact hsub.integrable_indicator measurableSet_Ioi

/-- The bilateral transform of the actual source remainder equals Ford's
pole-subtracted transform. -/
theorem laplaceTransformBilateral_fordLaplaceRemainder_eq
    {f : ℝ → ℝ} {z : ℂ} (hz : 0 < z.re)
    (hf : IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f y : ℂ)) (Ioi 0)) :
    laplaceTransformBilateral (fordLaplaceRemainder f) z =
      fordLaplaceF0 f z := by
  have hconst := integrableOn_ford_complex_exponential hz
  have hconstMul : IntegrableOn (fun y : ℝ =>
      Complex.exp (-z * (y : ℂ)) * (f 0 : ℂ)) (Ioi 0) :=
    hconst.mul_const (f 0 : ℂ)
  rw [laplaceTransformBilateral]
  have hindicator :
      (fun y : ℝ => Complex.exp (-z * (y : ℂ)) • fordLaplaceRemainder f y) =
        (Ioi (0 : ℝ)).indicator (fun y : ℝ =>
          Complex.exp (-z * (y : ℂ)) * ((f y : ℂ) - (f 0 : ℂ))) := by
    funext y
    by_cases hy : 0 < y
    · simp [fordLaplaceRemainder, hy, smul_eq_mul]
    · simp [fordLaplaceRemainder, hy]
  rw [hindicator, integral_indicator measurableSet_Ioi]
  simp_rw [mul_sub]
  rw [integral_sub hf hconstMul]
  rw [fordLaplaceF0, fordLaplaceTransform]
  rw [integral_mul_const]
  rw [integral_ford_complex_exponential hz]
  ring

/-- At the positive logarithms occurring in Ford's Dirichlet series, the
bilateral source is exactly `f(log n) - f(0)`. -/
theorem fordLaplaceRemainder_log_nat
    (f : ℝ → ℝ) {n : ℕ} (hn : 1 < n) :
    fordLaplaceRemainder f (Real.log n) =
      ((f (Real.log n) - f 0 : ℝ) : ℂ) := by
  rw [fordLaplaceRemainder, if_pos]
  exact Real.log_pos (by exact_mod_cast hn)

/-- On a symmetric window of radius `log n / 2`, the one-sided remainder
never meets its cutoff at zero.  Thus continuity of the source on the
positive ray gives exactly the local continuity needed for inversion. -/
theorem continuousOn_fordLaplaceRemainder_log_nat
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    {n : ℕ} (hn : 1 < n) :
    ContinuousOn (fordLaplaceRemainder f)
      (Set.Icc (Real.log n - Real.log n / 2)
        (Real.log n + Real.log n / 2)) := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hsub : Set.Icc (Real.log n - Real.log n / 2)
      (Real.log n + Real.log n / 2) ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    rw [Set.mem_Icc] at hy
    rw [Set.mem_Ioi]
    linarith
  have hreal : ContinuousOn (fun y : ℝ => f y - f 0)
      (Set.Icc (Real.log n - Real.log n / 2)
        (Real.log n + Real.log n / 2)) :=
    (hf.mono hsub).sub continuousOn_const
  have hcomplex : ContinuousOn (fun y : ℝ => ((f y - f 0 : ℝ) : ℂ))
      (Set.Icc (Real.log n - Real.log n / 2)
        (Real.log n + Real.log n / 2)) :=
    Complex.continuous_ofReal.comp_continuousOn hreal
  refine hcomplex.congr ?_
  intro y hy
  rw [fordLaplaceRemainder, if_pos]
  exact hsub hy

/-- Differentiability of the positive-ray source at `log n` transfers to
Ford's one-sided remainder because `log n > 0`. -/
theorem differentiableAt_fordLaplaceRemainder_log_nat
    {f : ℝ → ℝ} {n : ℕ} (hn : 1 < n)
    (hf : DifferentiableAt ℝ f (Real.log n)) :
    DifferentiableAt ℝ (fordLaplaceRemainder f) (Real.log n) := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have heq : fordLaplaceRemainder f =ᶠ[𝓝 (Real.log n)]
      (fun y : ℝ => ((f y - f 0 : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hlog] with y hy
    have hy' : 0 < y := hy
    rw [fordLaplaceRemainder, if_pos hy']
  have htarget : DifferentiableAt ℝ
      (fun y : ℝ => ((f y - f 0 : ℝ) : ℂ)) (Real.log n) := by
    exact Complex.ofRealCLM.differentiable.differentiableAt.comp _
      (hf.sub_const (f 0))
  exact htarget.congr_of_eventuallyEq heq

end

end GafniTao
