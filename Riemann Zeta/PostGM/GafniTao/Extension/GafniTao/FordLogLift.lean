import GafniTao.FordZeroDetectorPhysicalEdges

/-!
# An explicit interval logarithm lift for Ford's contour

The source proof chooses a branch of `log ζ` on a cut rectangle.  For the
edgewise integration by parts used below it is enough, and more explicit, to
construct the branch on a real parameter interval by integrating the actual
logarithmic derivative.  This file records that construction without a
global branch-choice axiom.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

/-- The logarithm lift starting with the value `ell₀` at parameter `a`. -/
def intervalLogLift (ell₀ : ℂ) (L : ℝ → ℂ) (a x : ℝ) : ℂ :=
  ell₀ + ∫ u in a..x, L u

@[simp]
theorem intervalLogLift_self (ell₀ : ℂ) (L : ℝ → ℂ) (a : ℝ) :
    intervalLogLift ell₀ L a a = ell₀ := by
  simp [intervalLogLift]

theorem hasDerivAt_intervalLogLift
    (ell₀ : ℂ) {L : ℝ → ℂ} (hL : Continuous L) (a x : ℝ) :
    HasDerivAt (intervalLogLift ell₀ L a) (L x) x := by
  unfold intervalLogLift
  exact (intervalIntegral.integral_hasDerivAt_right
    (hL.intervalIntegrable a x)
    (hL.stronglyMeasurableAtFilter volume (nhds x))
    hL.continuousAt).const_add ell₀

theorem continuous_intervalLogLift
    (ell₀ : ℂ) {L : ℝ → ℂ} (hL : Continuous L) (a : ℝ) :
    Continuous (intervalLogLift ell₀ L a) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (hasDerivAt_intervalLogLift ell₀ hL a x).continuousAt

/-- A zero-free differentiable function whose logarithmic derivative is `L`
is the exponential of the explicit lift, provided the initial value matches.
The proof differentiates `exp (-lift) * f` and applies the real interval FTC. -/
theorem exp_intervalLogLift_eq
    {f L : ℝ → ℂ} {ell₀ : ℂ} (a x : ℝ)
    (hL : Continuous L)
    (hf : ∀ y : ℝ, HasDerivAt f (f y * L y) y)
    (hbase : Complex.exp ell₀ = f a) :
    Complex.exp (intervalLogLift ell₀ L a x) = f x := by
  let ell : ℝ → ℂ := intervalLogLift ell₀ L a
  let q : ℝ → ℂ := fun y => Complex.exp (-ell y) * f y
  have hq : ∀ y : ℝ, HasDerivAt q 0 y := by
    intro y
    have hell : HasDerivAt ell (L y) y := by
      exact hasDerivAt_intervalLogLift ell₀ hL a y
    have hprod := hell.neg.cexp.mul (hf y)
    dsimp only [q]
    convert hprod using 1
    ring
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a x :=
    continuous_const.intervalIntegrable a x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := x)
    (f := q) (f' := fun _ : ℝ => (0 : ℂ))
    (fun y _hy => hq y) hzero
  have hqa : q a = 1 := by
    dsimp only [q, ell]
    rw [intervalLogLift_self, ← hbase]
    rw [← Complex.exp_add]
    simp
  have hqx : q x = 1 := by
    apply sub_eq_zero.mp
    simpa [hqa] using hFTC.symm
  calc
    Complex.exp (intervalLogLift ell₀ L a x) =
        Complex.exp (intervalLogLift ell₀ L a x) * 1 := by simp
    _ = Complex.exp (intervalLogLift ell₀ L a x) * q x := by rw [hqx]
    _ = f x := by
      dsimp only [q, ell]
      rw [← mul_assoc, ← Complex.exp_add]
      simp

theorem re_intervalLogLift_eq_log_norm
    {f L : ℝ → ℂ} {ell₀ : ℂ} (a x : ℝ)
    (hL : Continuous L)
    (hf : ∀ y : ℝ, HasDerivAt f (f y * L y) y)
    (hbase : Complex.exp ell₀ = f a) :
    (intervalLogLift ell₀ L a x).re = Real.log ‖f x‖ := by
  have hexp := exp_intervalLogLift_eq a x hL hf hbase
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp] at hnorm
  calc
    (intervalLogLift ell₀ L a x).re =
        Real.log (Real.exp (intervalLogLift ell₀ L a x).re) := by
      rw [Real.log_exp]
    _ = Real.log ‖f x‖ := by rw [hnorm]

/-- Canonical initial choice for the explicit interval lift. -/
def canonicalIntervalLogLift (f L : ℝ → ℂ) (a x : ℝ) : ℂ :=
  intervalLogLift (Complex.log (f a)) L a x

@[simp]
theorem canonicalIntervalLogLift_self
    (f L : ℝ → ℂ) (a : ℝ) :
    canonicalIntervalLogLift f L a a = Complex.log (f a) := by
  simp [canonicalIntervalLogLift]

theorem exp_canonicalIntervalLogLift_eq
    {f L : ℝ → ℂ} (a x : ℝ)
    (hL : Continuous L)
    (hf : ∀ y : ℝ, HasDerivAt f (f y * L y) y)
    (hfa : f a ≠ 0) :
    Complex.exp (canonicalIntervalLogLift f L a x) = f x := by
  exact exp_intervalLogLift_eq a x hL hf (Complex.exp_log hfa)

theorem re_canonicalIntervalLogLift_eq_log_norm
    {f L : ℝ → ℂ} (a x : ℝ)
    (hL : Continuous L)
    (hf : ∀ y : ℝ, HasDerivAt f (f y * L y) y)
    (hfa : f a ≠ 0) :
    (canonicalIntervalLogLift f L a x).re = Real.log ‖f x‖ := by
  exact re_intervalLogLift_eq_log_norm a x hL hf (Complex.exp_log hfa)

/-- Exact edgewise integration by parts with the explicit logarithm lift.
The endpoint terms are retained; on a closed cut contour they cancel against
the adjacent edges rather than being discarded. -/
theorem integral_mul_logDerivative_eq_boundary_sub_logLift
    {h h' L : ℝ → ℂ} (ell₀ : ℂ) (a b : ℝ)
    (hh : ∀ x : ℝ, HasDerivAt h (h' x) x)
    (hh' : Continuous h') (hL : Continuous L) :
    (∫ x in a..b, h x * L x) =
      h b * intervalLogLift ell₀ L a b - h a * ell₀ -
        ∫ x in a..b, h' x * intervalLogLift ell₀ L a x := by
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b)
    (u := h) (v := intervalLogLift ell₀ L a)
    (u' := h') (v' := L)
    (fun x _hx => hh x)
    (fun x _hx => hasDerivAt_intervalLogLift ell₀ hL a x)
    (hh'.intervalIntegrable a b)
    (hL.intervalIntegrable a b)
  simpa using hip

theorem integral_mul_logDerivative_eq_boundary_sub_canonicalLogLift
    {f h h' L : ℝ → ℂ} (a b : ℝ)
    (hh : ∀ x : ℝ, HasDerivAt h (h' x) x)
    (hh' : Continuous h') (hL : Continuous L) :
    (∫ x in a..b, h x * L x) =
      h b * canonicalIntervalLogLift f L a b -
        h a * Complex.log (f a) -
        ∫ x in a..b, h' x * canonicalIntervalLogLift f L a x := by
  exact integral_mul_logDerivative_eq_boundary_sub_logLift
    (Complex.log (f a)) a b hh hh' hL

end

end GafniTao
