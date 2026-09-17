import Tao2026.SmoothNumberSaddleTilt
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The smooth saddle as a probability law

The tilted masses are realized here as a discrete probability measure on the
logarithmic sizes of positive smooth integers.  This supplies the literal
characteristic function needed for Fourier inversion and the local central
limit argument.
-/

open MeasureTheory

namespace Tao2026

noncomputable section

/-- The tilted probability law of `log n`, supported on positive
`y`-smooth integers. -/
noncomputable def smoothTiltedLogMeasure (y : ℕ) (sigma : ℝ) : Measure ℝ :=
  Measure.sum fun n : Nat.smoothNumbers (y + 1) =>
    ENNReal.ofReal (smoothTiltedMass y sigma n) •
      Measure.dirac (Real.log (n.1 : ℝ))

/-- The summable tilted masses have sum one in `HasSum` form. -/
theorem hasSum_smoothTiltedMass_eq_one
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasSum (smoothTiltedMass y sigma) 1 := by
  have h := (summable_smoothTiltedMass y hsigma).hasSum
  rw [tsum_smoothTiltedMass_eq_one y hsigma] at h
  exact h

/-- The tilted logarithmic measure is a probability measure. -/
theorem isProbabilityMeasure_smoothTiltedLogMeasure
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    IsProbabilityMeasure (smoothTiltedLogMeasure y sigma) := by
  unfold smoothTiltedLogMeasure
  exact (hasSum_smoothTiltedMass_eq_one y hsigma).isProbabilityMeasure_sum_dirac
    (fun n => (smoothTiltedMass_pos y hsigma n).le)

/-- The characteristic function of the tilted logarithmic law. -/
noncomputable def smoothTiltedCharacteristic
    (y : ℕ) (sigma t : ℝ) : ℂ :=
  charFun (smoothTiltedLogMeasure y sigma) t

/-- The tilted characteristic function equals one at the origin. -/
@[simp]
theorem smoothTiltedCharacteristic_zero
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothTiltedCharacteristic y sigma 0 = 1 := by
  letI : IsProbabilityMeasure (smoothTiltedLogMeasure y sigma) :=
    isProbabilityMeasure_smoothTiltedLogMeasure y hsigma
  simp [smoothTiltedCharacteristic]

/-- Every value of the tilted characteristic function has norm at most one. -/
theorem norm_smoothTiltedCharacteristic_le_one
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    ‖smoothTiltedCharacteristic y sigma t‖ ≤ 1 := by
  letI : IsProbabilityMeasure (smoothTiltedLogMeasure y sigma) :=
    isProbabilityMeasure_smoothTiltedLogMeasure y hsigma
  exact norm_charFun_le_one t

/-- The Fourier series defining the tilted characteristic function is
absolutely summable. -/
theorem summable_smoothTiltedFourierSeries
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    Summable fun n : Nat.smoothNumbers (y + 1) =>
      (smoothTiltedMass y sigma n : ℂ) *
        Complex.exp ((t * Real.log (n.1 : ℝ) : ℝ) * Complex.I) := by
  apply Summable.of_norm
  refine (summable_smoothTiltedMass y hsigma).congr (fun n => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (smoothTiltedMass_pos y hsigma n)]
  have hexp :
      ‖Complex.exp
        (((t * Real.log (n.1 : ℝ) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I (t * Real.log (n.1 : ℝ))
  rw [hexp, mul_one]

/-- The characteristic function is the absolutely convergent Fourier series
of the explicit tilted masses. -/
theorem smoothTiltedCharacteristic_eq_tsum
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    smoothTiltedCharacteristic y sigma t =
      ∑' n : Nat.smoothNumbers (y + 1),
        (smoothTiltedMass y sigma n : ℂ) *
          Complex.exp ((t * Real.log (n.1 : ℝ) : ℝ) * Complex.I) := by
  rw [smoothTiltedCharacteristic, charFun_apply_real]
  unfold smoothTiltedLogMeasure
  rw [integral_sum_dirac_eq_tsum]
  · congr with n
    rw [ENNReal.toReal_ofReal (smoothTiltedMass_pos y hsigma n).le]
    rw [Complex.real_smul]
    rw [Complex.ofReal_mul]
  · intro n
    simp
  · refine (summable_smoothTiltedMass y hsigma).congr (fun n => ?_)
    rw [ENNReal.toReal_ofReal (smoothTiltedMass_pos y hsigma n).le]
    have hexp :
        ‖Complex.exp
          ((t : ℂ) * (Real.log (n.1 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [← Complex.ofReal_mul]
      exact Complex.norm_exp_ofReal_mul_I
        (t * Real.log (n.1 : ℝ))
    rw [hexp, mul_one]

/-- At the saddle, the first logarithmic derivative is exactly minus the
logarithmic cutoff.  This is the exact centering identity for the tilted
law. -/
theorem hasDerivAt_smoothTiltedLogPartition_at_saddle
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    HasDerivAt (smoothTiltedLogPartition y) (-Real.log X)
      (smoothSaddlePoint X y) := by
  simpa [smoothSaddlePhiOne_smoothSaddlePoint hX hy] using
    hasDerivAt_smoothTiltedLogPartition y
      (smoothSaddlePoint_pos hX hy)

/-- At the saddle, the derivative of the first log derivative is the
positive curvature used to normalize the Gaussian limit. -/
theorem hasDerivAt_deriv_smoothTiltedLogPartition_at_saddle
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    HasDerivAt (fun s => deriv (smoothTiltedLogPartition y) s)
      (smoothSaddlePhiTwo y (smoothSaddlePoint X y))
      (smoothSaddlePoint X y) :=
  hasDerivAt_deriv_smoothTiltedLogPartition y
    (smoothSaddlePoint_pos hX hy)

/-- The standard-deviation scale dictated by the saddle curvature. -/
noncomputable def smoothSaddleStandardDeviation (X y : ℕ) : ℝ :=
  Real.sqrt (smoothSaddlePhiTwo y (smoothSaddlePoint X y))

/-- The saddle standard deviation is positive in the defining range. -/
theorem smoothSaddleStandardDeviation_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddleStandardDeviation X y := by
  exact Real.sqrt_pos.2
    (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy))

/-- The characteristic function after exact saddle centering and variance
normalization. -/
noncomputable def smoothSaddleNormalizedCharacteristic
    (X y : ℕ) (t : ℝ) : ℂ :=
  Complex.exp
      ((-(t * Real.log X / smoothSaddleStandardDeviation X y) : ℝ) *
        Complex.I) *
    smoothTiltedCharacteristic y (smoothSaddlePoint X y)
      (t / smoothSaddleStandardDeviation X y)

/-- The normalized saddle characteristic function equals one at zero. -/
@[simp]
theorem smoothSaddleNormalizedCharacteristic_zero
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleNormalizedCharacteristic X y 0 = 1 := by
  simp [smoothSaddleNormalizedCharacteristic,
    smoothTiltedCharacteristic_zero y (smoothSaddlePoint_pos hX hy)]

/-- The normalized saddle characteristic function remains bounded by one. -/
theorem norm_smoothSaddleNormalizedCharacteristic_le_one
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    ‖smoothSaddleNormalizedCharacteristic X y t‖ ≤ 1 := by
  rw [smoothSaddleNormalizedCharacteristic, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_smoothTiltedCharacteristic_le_one y
    (smoothSaddlePoint_pos hX hy) _

/-- The normalized characteristic function is the explicit Fourier series
of the centered logarithmic variable at the saddle scale. -/
theorem smoothSaddleNormalizedCharacteristic_eq_tsum
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    smoothSaddleNormalizedCharacteristic X y t =
      ∑' n : Nat.smoothNumbers (y + 1),
        (smoothTiltedMass y (smoothSaddlePoint X y) n : ℂ) *
          Complex.exp
            (((t * (Real.log (n.1 : ℝ) - Real.log X) /
              smoothSaddleStandardDeviation X y : ℝ)) * Complex.I) := by
  rw [smoothSaddleNormalizedCharacteristic,
    smoothTiltedCharacteristic_eq_tsum y
      (smoothSaddlePoint_pos hX hy)]
  have hsum := summable_smoothTiltedFourierSeries y
    (smoothSaddlePoint_pos hX hy)
    (t / smoothSaddleStandardDeviation X y)
  rw [← hsum.tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    Complex.exp
          ((-(t * Real.log X / smoothSaddleStandardDeviation X y) : ℝ) *
            Complex.I) *
        ((smoothTiltedMass y (smoothSaddlePoint X y) n : ℂ) *
          Complex.exp
            (((t / smoothSaddleStandardDeviation X y) *
              Real.log (n.1 : ℝ) : ℝ) * Complex.I)) =
        (smoothTiltedMass y (smoothSaddlePoint X y) n : ℂ) *
          (Complex.exp
              ((-(t * Real.log X / smoothSaddleStandardDeviation X y) : ℝ) *
                Complex.I) *
            Complex.exp
              (((t / smoothSaddleStandardDeviation X y) *
                Real.log (n.1 : ℝ) : ℝ) * Complex.I)) := by ring
    _ = (smoothTiltedMass y (smoothSaddlePoint X y) n : ℂ) *
          Complex.exp
            (((t * (Real.log (n.1 : ℝ) - Real.log X) /
              smoothSaddleStandardDeviation X y : ℝ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

end

end Tao2026
