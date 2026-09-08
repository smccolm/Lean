import GafniTao.FordTrigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Ford's hyperbolic Fourier-kernel formula

The function below is the closed form of Ford's `U(y)`.  This file proves
the sign, parity and sharp uniform bound used after the contour-integral
evaluation.  The integral-to-formula theorem is kept as a separate analytic
obligation rather than being hidden in the definition.
-/

namespace GafniTao

/-- Ford's kernel `U(y) = π y / sinh (π y / 2)`, continuously extended
by `U(0)=2`. -/
noncomputable def fordFourierKernel (y : ℝ) : ℝ :=
  if y = 0 then 2 else Real.pi * y / Real.sinh (Real.pi * y / 2)

theorem fordFourierKernel_zero : fordFourierKernel 0 = 2 := by
  simp [fordFourierKernel]

theorem fordFourierKernel_of_ne {y : ℝ} (hy : y ≠ 0) :
    fordFourierKernel y = Real.pi * y / Real.sinh (Real.pi * y / 2) := by
  simp [fordFourierKernel, hy]

theorem fordFourierKernel_neg (y : ℝ) :
    fordFourierKernel (-y) = fordFourierKernel y := by
  by_cases hy : y = 0
  · simp [hy, fordFourierKernel]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    rw [fordFourierKernel_of_ne hny, fordFourierKernel_of_ne hy]
    rw [show Real.pi * -y / 2 = -(Real.pi * y / 2) by ring, Real.sinh_neg]
    ring

private theorem fordFourierKernel_nonneg_of_pos {y : ℝ} (hy : 0 < y) :
    0 ≤ fordFourierKernel y := by
  rw [fordFourierKernel_of_ne hy.ne']
  exact div_nonneg (mul_nonneg Real.pi_pos.le hy.le)
    (Real.sinh_nonneg_iff.mpr (by positivity))

theorem fordFourierKernel_nonneg (y : ℝ) :
    0 ≤ fordFourierKernel y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [← fordFourierKernel_neg y]
    exact fordFourierKernel_nonneg_of_pos (neg_pos.mpr hy)
  · simp [hy, fordFourierKernel]
  · exact fordFourierKernel_nonneg_of_pos hy

theorem fordFourierKernel_pos (y : ℝ) :
    0 < fordFourierKernel y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [← fordFourierKernel_neg y, fordFourierKernel_of_ne (neg_ne_zero.mpr hy.ne)]
    exact div_pos (mul_pos Real.pi_pos (neg_pos.mpr hy))
      (Real.sinh_pos_iff.mpr
        (div_pos (mul_pos Real.pi_pos (neg_pos.mpr hy)) (by norm_num)))
  · simp [hy, fordFourierKernel]
  · rw [fordFourierKernel_of_ne hy.ne']
    exact div_pos (mul_pos Real.pi_pos hy)
      (Real.sinh_pos_iff.mpr (by positivity))

private theorem fordFourierKernel_le_two_of_pos {y : ℝ} (hy : 0 < y) :
    fordFourierKernel y ≤ 2 := by
  rw [fordFourierKernel_of_ne hy.ne']
  have hx : 0 ≤ Real.pi * y / 2 := by positivity
  have hsinh : 0 < Real.sinh (Real.pi * y / 2) :=
    Real.sinh_pos_iff.mpr (by positivity)
  apply (div_le_iff₀ hsinh).2
  have h := Real.self_le_sinh_iff.mpr hx
  nlinarith

theorem fordFourierKernel_le_two (y : ℝ) : fordFourierKernel y ≤ 2 := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [← fordFourierKernel_neg y]
    exact fordFourierKernel_le_two_of_pos (neg_pos.mpr hy)
  · simp [hy, fordFourierKernel]
  · exact fordFourierKernel_le_two_of_pos hy

theorem fordFourierKernel_mem_Icc (y : ℝ) :
    fordFourierKernel y ∈ Set.Icc 0 2 :=
  ⟨fordFourierKernel_nonneg y, fordFourierKernel_le_two y⟩

/-- Beta-function evaluation underlying Ford's contour-integral formula.
This is the algebraic half of the `sech²` Fourier-transform calculation. -/
theorem ford_beta_kernel_value {y : ℝ} (hy : y ≠ 0) :
    2 * Complex.betaIntegral
        (1 + Complex.I * ((y : ℂ) / 2))
        (1 - Complex.I * ((y : ℂ) / 2)) =
      (fordFourierKernel y : ℂ) := by
  have hz : Complex.I * ((y : ℂ) / 2) ≠ 0 := by
    simp [hy]
  have hrePlus : 0 < (1 + Complex.I * ((y : ℂ) / 2)).re := by simp
  have hreMinus : 0 < (1 - Complex.I * ((y : ℂ) / 2)).re := by simp
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hrePlus hreMinus]
  have hsum :
      (1 + Complex.I * ((y : ℂ) / 2)) +
          (1 - Complex.I * ((y : ℂ) / 2)) = 2 := by ring
  rw [hsum]
  norm_num [Complex.Gamma_nat_eq_factorial]
  rw [show (1 + Complex.I * ((y : ℂ) / 2)) =
      Complex.I * ((y : ℂ) / 2) + 1 by ring,
    Complex.Gamma_add_one _ hz]
  rw [mul_assoc (Complex.I * ((y : ℂ) / 2)),
    Complex.Gamma_mul_Gamma_one_sub (Complex.I * ((y : ℂ) / 2))]
  rw [show (Real.pi : ℂ) * (Complex.I * ((y : ℂ) / 2)) =
      ((Real.pi : ℂ) * ((y : ℂ) / 2)) * Complex.I by ring,
    Complex.sin_mul_I]
  rw [fordFourierKernel_of_ne hy]
  push_cast
  field_simp [Real.sinh_ne_zero.mpr (by positivity : Real.pi * y / 2 ≠ 0)]

private theorem ford_sigmoid_log_odds (u : ℝ) :
    Real.log (Real.sigmoid (2 * u)) -
        Real.log (1 - Real.sigmoid (2 * u)) = 2 * u := by
  rw [← Real.sigmoid_neg, Real.sigmoid_def, Real.sigmoid_def]
  rw [Real.log_inv, Real.log_inv]
  have hOneExp : 1 + Real.exp (-2 * u) ≠ 0 := by positivity
  have hFactor : 1 + Real.exp (- -(2 * u)) =
      Real.exp (2 * u) * (1 + Real.exp (-2 * u)) := by
    rw [neg_neg]
    rw [mul_add, mul_one, ← Real.exp_add]
    rw [show 2 * u + -2 * u = 0 by ring, Real.exp_zero]
    ring
  rw [hFactor, Real.log_mul (Real.exp_ne_zero _) hOneExp, Real.log_exp]
  ring_nf

/-- The complex powers in the beta integrand become the Fourier phase under
the scaled logistic substitution. -/
theorem ford_sigmoid_cpow_phase (u y : ℝ) :
    ((Real.sigmoid (2 * u) : ℝ) : ℂ) ^
          (Complex.I * ((y : ℂ) / 2)) *
        (((1 - Real.sigmoid (2 * u) : ℝ) : ℂ) ^
          (-(Complex.I * ((y : ℂ) / 2)))) =
      Complex.exp (Complex.I * (y * u)) := by
  have hs : 0 < Real.sigmoid (2 * u) := Real.sigmoid_pos _
  have hsc : ((Real.sigmoid (2 * u) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hs.ne'
  have h1s : 0 < 1 - Real.sigmoid (2 * u) := sub_pos.mpr (Real.sigmoid_lt_one _)
  have h1sc : (((1 - Real.sigmoid (2 * u) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr h1s.ne'
  rw [Complex.cpow_def_of_ne_zero hsc, Complex.cpow_def_of_ne_zero h1sc,
    ← Complex.exp_add]
  rw [← Complex.ofReal_log hs.le, ← Complex.ofReal_log h1s.le]
  congr 1
  calc
    ((Real.log (Real.sigmoid (2 * u)) : ℂ) *
          (Complex.I * ((y : ℂ) / 2)) +
        (Real.log (1 - Real.sigmoid (2 * u)) : ℂ) *
          (-(Complex.I * ((y : ℂ) / 2)))) =
        Complex.I * ((y : ℂ) / 2) *
          ((Real.log (Real.sigmoid (2 * u)) : ℂ) -
            (Real.log (1 - Real.sigmoid (2 * u)) : ℂ)) := by ring
    _ = Complex.I * ((y : ℂ) / 2) * (2 * u : ℝ) := by
      rw [← Complex.ofReal_sub, ford_sigmoid_log_odds]
    _ = Complex.I * (y * u) := by push_cast; ring

theorem ford_two_sigmoid_mul_one_sub (u : ℝ) :
    2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u)) =
      1 / (2 * Real.cosh u ^ 2) := by
  rw [Real.sigmoid_def, Real.cosh_eq]
  have heu : Real.exp u ≠ 0 := Real.exp_ne_zero _
  have htwo : Real.exp (-(2 * u)) = (Real.exp u)⁻¹ ^ 2 := by
    rw [show -(2 * u) = -u + -u by ring, Real.exp_add, Real.exp_neg]
    ring
  rw [htwo, Real.exp_neg]
  field_simp [heu]
  ring

noncomputable def fordBetaKernelIntegrand (y x : ℝ) : ℂ :=
  (x : ℂ) ^ (Complex.I * ((y : ℂ) / 2)) *
    ((1 - x : ℝ) : ℂ) ^ (-(Complex.I * ((y : ℂ) / 2)))

noncomputable def fordSechFourierIntegrand (y u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2

/-- Pointwise Jacobian identity for the scaled logistic substitution from
the real line to `(0,1)`. -/
theorem ford_sigmoid_beta_jacobian (u y : ℝ) :
    (2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u))) •
        fordBetaKernelIntegrand y (Real.sigmoid (2 * u)) =
      (1 / 2 : ℝ) • fordSechFourierIntegrand y u := by
  rw [fordBetaKernelIntegrand, ford_sigmoid_cpow_phase,
    ford_two_sigmoid_mul_one_sub]
  simp only [fordSechFourierIntegrand, Complex.real_smul]
  have hcosh : (Real.cosh u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne'
  push_cast
  field_simp [hcosh]

private theorem ford_scaled_sigmoid_image :
    (fun u : ℝ => Real.sigmoid (2 * u)) '' Set.univ = Set.Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨u, _hu, rfl⟩
    exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩
  · intro hx
    rw [← Real.range_sigmoid] at hx
    obtain ⟨v, rfl⟩ := hx
    refine ⟨v / 2, Set.mem_univ _, ?_⟩
    exact congrArg Real.sigmoid (by ring)

private theorem ford_scaled_sigmoid_injOn :
    Set.InjOn (fun u : ℝ => Real.sigmoid (2 * u)) Set.univ := by
  intro x _hx y _hy hxy
  apply (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0))
  exact Real.sigmoid_injective hxy

private theorem ford_scaled_sigmoid_hasDerivWithinAt (u : ℝ) :
    HasDerivWithinAt (fun v : ℝ => Real.sigmoid (2 * v))
      (2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u)))
      Set.univ u := by
  convert (Real.hasDerivAt_sigmoid (2 * u)).comp u
      ((hasDerivAt_id u).const_mul 2) |>.hasDerivWithinAt using 1
  ring

private theorem ford_betaIntegral_eq_setIntegral (y : ℝ) :
    Complex.betaIntegral
        (1 + Complex.I * ((y : ℂ) / 2))
        (1 - Complex.I * ((y : ℂ) / 2)) =
      ∫ x in Set.Ioo (0 : ℝ) 1, fordBetaKernelIntegrand y x := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro x _hx
  simp only [fordBetaKernelIntegrand]
  push_cast
  ring_nf

/-- Exact logistic change of variables from Ford's beta integral to the
Fourier transform of `1 / cosh²`. -/
theorem ford_betaIntegral_eq_half_sechFourierIntegral (y : ℝ) :
    Complex.betaIntegral
        (1 + Complex.I * ((y : ℂ) / 2))
        (1 - Complex.I * ((y : ℂ) / 2)) =
      (1 / 2 : ℝ) • ∫ u : ℝ, fordSechFourierIntegrand y u := by
  have hChange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => Real.sigmoid (2 * u))
    (f' := fun u : ℝ =>
      2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u)))
    MeasurableSet.univ
    (fun u _hu => ford_scaled_sigmoid_hasDerivWithinAt u)
    ford_scaled_sigmoid_injOn (fordBetaKernelIntegrand y)
  rw [ford_scaled_sigmoid_image] at hChange
  have hChange' :
      (∫ x in Set.Ioo (0 : ℝ) 1, fordBetaKernelIntegrand y x) =
        ∫ u : ℝ,
          |2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u))| •
            fordBetaKernelIntegrand y (Real.sigmoid (2 * u)) := by
    simpa using hChange
  calc
    Complex.betaIntegral
        (1 + Complex.I * ((y : ℂ) / 2))
        (1 - Complex.I * ((y : ℂ) / 2)) =
        ∫ x in Set.Ioo (0 : ℝ) 1, fordBetaKernelIntegrand y x :=
      ford_betaIntegral_eq_setIntegral y
    _ = ∫ u : ℝ,
        |2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u))| •
          fordBetaKernelIntegrand y (Real.sigmoid (2 * u)) := hChange'
    _ = ∫ u : ℝ, (1 / 2 : ℝ) • fordSechFourierIntegrand y u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with u
      have hnonneg :
          0 ≤ 2 * Real.sigmoid (2 * u) * (1 - Real.sigmoid (2 * u)) :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.sigmoid_nonneg _))
          (sub_nonneg.mpr (Real.sigmoid_le_one _))
      rw [abs_of_nonneg hnonneg]
      exact ford_sigmoid_beta_jacobian u y
    _ = (1 / 2 : ℝ) • ∫ u : ℝ, fordSechFourierIntegrand y u := by
      rw [MeasureTheory.integral_smul]

theorem ford_two_mul_beta_kernel_value (y : ℝ) :
    2 * Complex.betaIntegral
        (1 + Complex.I * ((y : ℂ) / 2))
        (1 - Complex.I * ((y : ℂ) / 2)) =
      (fordFourierKernel y : ℂ) := by
  by_cases hy : y = 0
  · subst y
    rw [fordFourierKernel_zero]
    norm_num [Complex.betaIntegral_eval_one_right]
  · exact ford_beta_kernel_value hy

/-- Ford's displayed Fourier-transform identity, including the continuous
value at `y=0`. -/
theorem ford_sechFourierIntegral_eq_kernel (y : ℝ) :
    (∫ u : ℝ, fordSechFourierIntegrand y u) =
      (fordFourierKernel y : ℂ) := by
  have hBeta := ford_betaIntegral_eq_half_sechFourierIntegral y
  calc
    (∫ u : ℝ, fordSechFourierIntegrand y u) =
        2 * Complex.betaIntegral
          (1 + Complex.I * ((y : ℂ) / 2))
          (1 - Complex.I * ((y : ℂ) / 2)) := by
      rw [hBeta]
      simp only [Complex.real_smul]
      push_cast
      ring
    _ = (fordFourierKernel y : ℂ) := ford_two_mul_beta_kernel_value y

theorem ford_sechFourierIntegral_literal (y : ℝ) :
    (∫ u : ℝ,
        Complex.exp (Complex.I * (y * u)) / (Real.cosh u : ℂ) ^ 2) =
      (fordFourierKernel y : ℂ) := by
  simpa only [fordSechFourierIntegrand] using
    ford_sechFourierIntegral_eq_kernel y

/-- Absolute integrability is recovered from the exact nonzero transform.
This also records explicitly that the preceding change-of-variables identity
is not using the zero convention for a nonintegrable Bochner integrand. -/
theorem integrable_fordSechFourierIntegrand (y : ℝ) :
    MeasureTheory.Integrable (fordSechFourierIntegrand y) := by
  by_contra hInt
  have hZero : (∫ u : ℝ, fordSechFourierIntegrand y u) = 0 :=
    MeasureTheory.integral_undef hInt
  have hValue := ford_sechFourierIntegral_eq_kernel y
  rw [hZero] at hValue
  have hPos : (0 : ℂ) ≠ (fordFourierKernel y : ℂ) := by
    exact (Complex.ofReal_ne_zero.mpr (fordFourierKernel_pos y).ne').symm
  exact hPos hValue

/-- The translated real cosine transform needed term-by-term in Ford's
Euler-product proof. -/
theorem ford_integral_cos_add_mul_div_cosh_sq (a y : ℝ) :
    (∫ u : ℝ, Real.cos (a + y * u) / Real.cosh u ^ 2) =
      fordFourierKernel y * Real.cos a := by
  let F : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * (a + y * u)) / (Real.cosh u : ℂ) ^ 2
  have hPhase (u : ℝ) :
      F u = Complex.exp (Complex.I * a) * fordSechFourierIntegrand y u := by
    simp only [F, fordSechFourierIntegrand]
    rw [show Complex.I * ((a : ℂ) + (y : ℂ) * (u : ℂ)) =
        Complex.I * (a : ℂ) + Complex.I * ((y : ℂ) * (u : ℂ)) by ring,
      Complex.exp_add]
    ring
  have hFInt : MeasureTheory.Integrable F := by
    apply MeasureTheory.Integrable.congr
      ((integrable_fordSechFourierIntegrand y).const_mul
        (Complex.exp (Complex.I * a)))
    exact Filter.Eventually.of_forall fun u => (hPhase u).symm
  have hFValue :
      (∫ u : ℝ, F u) =
        Complex.exp (Complex.I * a) * (fordFourierKernel y : ℂ) := by
    calc
      (∫ u : ℝ, F u) =
          ∫ u : ℝ, Complex.exp (Complex.I * a) *
            fordSechFourierIntegrand y u := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hPhase
      _ = Complex.exp (Complex.I * a) *
          (∫ u : ℝ, fordSechFourierIntegrand y u) := by
        rw [MeasureTheory.integral_const_mul]
      _ = Complex.exp (Complex.I * a) * (fordFourierKernel y : ℂ) := by
        rw [ford_sechFourierIntegral_eq_kernel]
  have hRe (u : ℝ) :
      (F u).re = Real.cos (a + y * u) / Real.cosh u ^ 2 := by
    dsimp only [F]
    rw [show (Real.cosh u : ℂ) ^ 2 = ((Real.cosh u ^ 2 : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [Complex.div_ofReal_re]
    simp [Complex.exp_re]
  calc
    (∫ u : ℝ, Real.cos (a + y * u) / Real.cosh u ^ 2) =
        (∫ u : ℝ, (F u).re) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun u => (hRe u).symm
    _ = (∫ u : ℝ, F u).re := by
      simpa only [RCLike.re_to_complex] using (integral_re hFInt)
    _ = (Complex.exp (Complex.I * a) * (fordFourierKernel y : ℂ)).re := by
      rw [hFValue]
    _ = fordFourierKernel y * Real.cos a := by
      simp [Complex.exp_re, mul_comm]

theorem integrable_ford_cos_add_mul_div_cosh_sq (a y : ℝ) :
    MeasureTheory.Integrable
      (fun u : ℝ => Real.cos (a + y * u) / Real.cosh u ^ 2) := by
  let F : ℝ → ℂ := fun u =>
    Complex.exp (Complex.I * (a + y * u)) / (Real.cosh u : ℂ) ^ 2
  have hPhase (u : ℝ) :
      F u = Complex.exp (Complex.I * a) * fordSechFourierIntegrand y u := by
    simp only [F, fordSechFourierIntegrand]
    rw [show Complex.I * ((a : ℂ) + (y : ℂ) * (u : ℂ)) =
        Complex.I * (a : ℂ) + Complex.I * ((y : ℂ) * (u : ℂ)) by ring,
      Complex.exp_add]
    ring
  have hFInt : MeasureTheory.Integrable F := by
    apply MeasureTheory.Integrable.congr
      ((integrable_fordSechFourierIntegrand y).const_mul
        (Complex.exp (Complex.I * a)))
    exact Filter.Eventually.of_forall fun u => (hPhase u).symm
  have hRe (u : ℝ) :
      (F u).re = Real.cos (a + y * u) / Real.cosh u ^ 2 := by
    dsimp only [F]
    rw [show (Real.cosh u : ℂ) ^ 2 = ((Real.cosh u ^ 2 : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [Complex.div_ofReal_re]
    simp [Complex.exp_re]
  exact hFInt.re.congr (Filter.Eventually.of_forall hRe)

theorem integrable_one_div_cosh_sq :
    MeasureTheory.Integrable (fun u : ℝ => 1 / Real.cosh u ^ 2) := by
  simpa using integrable_ford_cos_add_mul_div_cosh_sq 0 0

theorem integral_one_div_cosh_sq :
    (∫ u : ℝ, 1 / Real.cosh u ^ 2) = 2 := by
  simpa [fordFourierKernel_zero] using
    ford_integral_cos_add_mul_div_cosh_sq 0 0

end GafniTao
