import TaoTrudgianYang2025.ZetaAtkinsonReducedSource

/-!
# Exact oscillatory carrier of the phase-adjusted divisor source

The actual smooth test is factored with its complex Mellin weight,
Gamma factor and quadratic Gaussian left in the amplitude. The real
carrier is differentiated without treating those factors as constants
in any subsequent integral estimate. The choices b = sqrt(n) and -sqrt(n) will
be needed after a separately proved Y0 asymptotic expansion.
-/

noncomputable section

open Complex

namespace TaoTrudgianYang2025

def zetaAtkinsonPhase (T b x : ℝ) : ℝ :=
  T * Real.log x - 2 * Real.pi * x + 4 * Real.pi * b * Real.sqrt x

def zetaAtkinsonAmplitude (T G L x : ℝ) : ℂ :=
  (zetaDivisorBandCutoff T G L x : ℂ) * (Real.exp (-Real.log x / 2) : ℂ) *
    zetaDivisorWeight ((Real.log x : ℂ) - zetaGammaLeadingLog T) *
      zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem ofReal_cpow_critical_conjugate (T : ℝ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((-1 / 2 : ℂ) + (T : ℂ) * I) =
      (Real.exp (-Real.log x / 2) : ℂ) * Complex.exp ((T * Real.log x : ℝ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem zetaAtkinsonDivisorTest_mul_carrier (T G L b : ℝ) {x : ℝ} (hx : 0 < x) :
    zetaAtkinsonDivisorTest T G L x *
      Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I) =
        zetaAtkinsonAmplitude T G L x * Complex.exp ((zetaAtkinsonPhase T b x : ℝ) * I) := by
  have hp : Complex.exp ((zetaAtkinsonPhase T b x : ℝ) * I) =
      Complex.exp ((-2 * Real.pi * x : ℝ) * I) *
        Complex.exp ((T * Real.log x : ℝ) * I) *
          Complex.exp ((4 * Real.pi * b * Real.sqrt x : ℝ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold zetaAtkinsonPhase
    push_cast
    ring
  rw [hp]
  unfold zetaAtkinsonDivisorTest zetaDivisorLatticePhase zetaSmoothDivisorTest
    zetaShortDivisorTestFunction zetaAtkinsonAmplitude
  rw [ofReal_cpow_critical_conjugate T hx]
  ring

theorem zetaAtkinsonDivisorTest_eq_amplitude_phase (T G L : ℝ) {x : ℝ} (hx : 0 < x) :
    zetaAtkinsonDivisorTest T G L x =
      zetaAtkinsonAmplitude T G L x * Complex.exp ((zetaAtkinsonPhase T 0 x : ℝ) * I) := by
  simpa only [mul_zero, zero_mul, ofReal_zero, Complex.exp_zero, mul_one] using
    zetaAtkinsonDivisorTest_mul_carrier T G L 0 hx

theorem hasDerivAt_zetaAtkinsonPhase (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaAtkinsonPhase T b)
      (T / x - 2 * Real.pi + 2 * Real.pi * b / Real.sqrt x) x := by
  have h := (((Real.hasDerivAt_log hx.ne').const_mul T).sub
    ((hasDerivAt_id x).const_mul (2 * Real.pi))).add
      ((Real.hasDerivAt_sqrt hx.ne').const_mul (4 * Real.pi * b))
  convert h using 1
  simp only [mul_one]
  ring

theorem hasDerivAt_zetaAtkinsonPhaseDerivative (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => T / y - 2 * Real.pi + 2 * Real.pi * b / Real.sqrt y)
      (-T / x ^ 2 - Real.pi * b / (Real.sqrt x) ^ 3) x := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have h := (((hasDerivAt_const x T).div (hasDerivAt_id x) hx.ne').sub_const (2 * Real.pi)).add
    ((hasDerivAt_const x (2 * Real.pi * b)).div (Real.hasDerivAt_sqrt hx.ne') hs)
  convert h using 1
  simp only [id_eq, zero_mul, mul_one, zero_sub]
  field_simp
  ring

theorem hasDerivAt_deriv_zetaAtkinsonPhase (T b : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (zetaAtkinsonPhase T b))
      (-T / x ^ 2 - Real.pi * b / (Real.sqrt x) ^ 3) x := by
  apply (hasDerivAt_zetaAtkinsonPhaseDerivative T b hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact (hasDerivAt_zetaAtkinsonPhase T b hy).deriv

end TaoTrudgianYang2025
