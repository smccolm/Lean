import RiemannZeta.GuthMaynard.HughesYoungCentralBetaBridge
import RiemannZeta.GuthMaynard.HughesYoungCentralArithmeticBridge

open Complex MeasureTheory Set
open scoped ContDiff Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The pole-cancelled Hughes--Young central contour

This module packages one literal `(r,q)` summand from Hughes--Young
equation (84) as a holomorphic function of the complex Mellin variable.
The completed-zeta zero is multiplied into the differentiated beta kernel
before any contour movement.  Consequently no meromorphic beta factor is
moved across its apparent pole in isolation.
-/

/-- The part of the reduced Mellin scale which does not contain the
completed-zeta contour weight.  Its dependence on `w` is through entire
exponentials only. -/
noncomputable def hughesYoungReducedMellinStaticComplex
    (T t : ℝ) (h k : ℕ) (w : ℂ) : ℂ :=
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
    shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
    (1 / (Real.pi : ℂ)) *
    Complex.exp (s₁ * (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)) *
    Complex.exp (s₂ * (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))

/-- Exact factorization of the concrete reduced Mellin scale on a vertical
line. -/
theorem hughesYoungReducedMellinScaleConstant_eq_static_mul_contour
    (T t c u : ℝ) (h k : ℕ) :
    hughesYoungReducedMellinScaleConstant T t c u h k =
      hughesYoungReducedMellinStaticComplex T t h k
          ((c : ℂ) + (u : ℂ) * I) *
        hughesYoungRightContourWeightComplex t
          ((c : ℂ) + (u : ℂ) * I) := by
  unfold hughesYoungReducedMellinScaleConstant
    hughesYoungReducedMellinStaticComplex hughesYoungMellinScalar
  rw [hughesYoungRightContourWeightComplex_vertical]
  ring

/-- The completed-zeta contour factor is invariant under exchanging the two
critical-line points. -/
theorem hughesYoungRightContourWeightComplex_neg
    (t : ℝ) (w : ℂ) :
    hughesYoungRightContourWeightComplex t w =
      hughesYoungRightContourWeightComplex (-t) w := by
  unfold hughesYoungRightContourWeightComplex afePoleNormalization
    afeGammaNormalization
  simp only [neg_neg]
  ring

/-- The entire realization of the positive-integer power `r^(-2w)`. -/
noncomputable def hughesYoungCentralShiftPower (r : ℕ) (w : ℂ) : ℂ :=
  Complex.exp ((-2 * w) * (Real.log (r : ℝ) : ℂ))

/-- On positive shifts the entire logarithmic realization agrees with the
complex power used in equation (84). -/
theorem hughesYoungCentralShiftPower_eq_cpow
    {r : ℕ} (hr : 0 < r) (w : ℂ) :
    hughesYoungCentralShiftPower r w = (r : ℂ) ^ (-2 * w) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold hughesYoungCentralShiftPower
  rw [Complex.cpow_def_of_ne_zero hrC]
  rw [Complex.natCast_log]
  ring_nf

/-- One positive-shift `(r,q)` summand after the completed-zeta zero has
regularized the equation-(84) beta kernel. -/
noncomputable def hughesYoungEquation84PositiveContourTerm
    (T t : ℝ) (h k a b r q : ℕ) (w : ℂ) : ℂ :=
  (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
    (hughesYoungReducedMellinStaticComplex T t h k w *
      hughesYoungCentralShiftPower r w *
      hughesYoungEquation84RegularizedContourKernel t w
        ((Real.log r : ℂ) +
          dfiEquation27LogConstant b (dfiReducedDenominator b q))
        ((Real.log r : ℂ) +
          dfiEquation27LogConstant a (dfiReducedDenominator a q)))

/-- The negative-shift coordinate-swapped companion. -/
noncomputable def hughesYoungEquation84NegativeContourTerm
    (T t : ℝ) (h k a b r q : ℕ) (w : ℂ) : ℂ :=
  (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
    (hughesYoungReducedMellinStaticComplex T t h k w *
      hughesYoungCentralShiftPower r w *
      hughesYoungEquation84RegularizedContourKernel (-t) w
        ((Real.log r : ℂ) +
          dfiEquation27LogConstant a (dfiReducedDenominator a q))
        ((Real.log r : ℂ) +
          dfiEquation27LogConstant b (dfiReducedDenominator b q)))

/-- Termwise identification of the positive equation-(84) summand with its
pole-cancelled holomorphic contour representative. -/
theorem hughesYoungEquation84Positive_summand_eq_contourTerm
    (T t u : ℝ) {c : ℝ} (hcHalf : c < 1 / 2)
    (h k a b : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
        (hughesYoungReducedMellinScaleConstant T t c u h k *
          (r : ℂ) ^ (-(2 * ((c : ℂ) + (u : ℂ) * I))) *
          hughesYoungEquation84CriticalBetaKernel t
            ((c : ℂ) + (u : ℂ) * I)
            ((Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q))
            ((Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q))) =
      hughesYoungEquation84PositiveContourTerm T t h k a b r q
        ((c : ℂ) + (u : ℂ) * I) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hz : 0 < (afeCriticalPoint t - w).re := by
    simp [w, afeCriticalPoint]
    linarith
  rw [hughesYoungReducedMellinScaleConstant_eq_static_mul_contour]
  rw [show -(2 * ((c : ℂ) + (u : ℂ) * I)) =
      -2 * ((c : ℂ) + (u : ℂ) * I) by ring]
  rw [← hughesYoungCentralShiftPower_eq_cpow hr
    ((c : ℂ) + (u : ℂ) * I)]
  have hreg :=
    hughesYoungRightContourWeightComplex_mul_equation84_eq_regularized
      (t := t) (w := w)
      (CX := (Real.log r : ℂ) +
        dfiEquation27LogConstant b (dfiReducedDenominator b q))
      (COne := (Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q)) hz
  unfold hughesYoungEquation84PositiveContourTerm
  simp only [w] at hreg
  calc
    _ = (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b r q) *
        (hughesYoungReducedMellinStaticComplex T t h k w *
          hughesYoungCentralShiftPower r w *
          (hughesYoungRightContourWeightComplex t w *
            hughesYoungEquation84CriticalBetaKernel t w
              ((Real.log r : ℂ) +
                dfiEquation27LogConstant b (dfiReducedDenominator b q))
              ((Real.log r : ℂ) +
                dfiEquation27LogConstant a (dfiReducedDenominator a q)))) := by ring
    _ = _ := by rw [hreg]

/-- Termwise identification of the negative equation-(84) summand with its
coordinate-swapped holomorphic representative. -/
theorem hughesYoungEquation84Negative_summand_eq_contourTerm
    (T t u : ℝ) {c : ℝ} (hcHalf : c < 1 / 2)
    (h k a b : ℕ) {r : ℕ} (hr : 0 < r) (q : ℕ) :
    (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
        (hughesYoungReducedMellinScaleConstant T t c u h k *
          (r : ℂ) ^ (-(2 * ((c : ℂ) + (u : ℂ) * I))) *
          hughesYoungEquation84CriticalBetaKernel (-t)
            ((c : ℂ) + (u : ℂ) * I)
            ((Real.log r : ℂ) +
              dfiEquation27LogConstant a (dfiReducedDenominator a q))
            ((Real.log r : ℂ) +
              dfiEquation27LogConstant b (dfiReducedDenominator b q))) =
      hughesYoungEquation84NegativeContourTerm T t h k a b r q
        ((c : ℂ) + (u : ℂ) * I) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hz : 0 < (afeCriticalPoint (-t) - w).re := by
    simp [w, afeCriticalPoint]
    linarith
  rw [hughesYoungReducedMellinScaleConstant_eq_static_mul_contour]
  rw [show -(2 * ((c : ℂ) + (u : ℂ) * I)) =
      -2 * ((c : ℂ) + (u : ℂ) * I) by ring]
  rw [← hughesYoungCentralShiftPower_eq_cpow hr
    ((c : ℂ) + (u : ℂ) * I)]
  rw [hughesYoungRightContourWeightComplex_neg t
    ((c : ℂ) + (u : ℂ) * I)]
  have hreg :=
    hughesYoungRightContourWeightComplex_mul_equation84_eq_regularized
      (t := -t) (w := w)
      (CX := (Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q))
      (COne := (Real.log r : ℂ) +
        dfiEquation27LogConstant b (dfiReducedDenominator b q)) hz
  unfold hughesYoungEquation84NegativeContourTerm
  simp only [w] at hreg
  calc
    _ = (((b : ℂ) * a)⁻¹ * dfiEquation27ArithmeticCoefficient b a r q) *
        (hughesYoungReducedMellinStaticComplex T t h k w *
          hughesYoungCentralShiftPower r w *
          (hughesYoungRightContourWeightComplex (-t) w *
            hughesYoungEquation84CriticalBetaKernel (-t) w
              ((Real.log r : ℂ) +
                dfiEquation27LogConstant a (dfiReducedDenominator a q))
              ((Real.log r : ℂ) +
                dfiEquation27LogConstant b (dfiReducedDenominator b q)))) := by ring
    _ = _ := by rw [hreg]

/-- The complete positive equation-(84) modulus series represented on a
complex contour line. -/
noncomputable def hughesYoungEquation84PositiveContourSeries
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) : ℂ :=
  ∑' q : ℕ,
    hughesYoungEquation84PositiveContourTerm T t h k a b r q w

/-- The complete negative equation-(84) modulus series on a complex
contour line. -/
noncomputable def hughesYoungEquation84NegativeContourSeries
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) : ℂ :=
  ∑' q : ℕ,
    hughesYoungEquation84NegativeContourTerm T t h k a b r q w

/-- Exact positive-series entry into the pole-cancelled contour. -/
theorem hughesYoungEquation84Positive_eq_contourSeries
    (T t u : ℝ) {c : ℝ} (hcHalf : c < 1 / 2)
    (h k a b : ℕ) {r : ℕ} (hr : 0 < r) :
    hughesYoungEquation84Positive T t c u h k a b r =
      hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I) := by
  unfold hughesYoungEquation84Positive
    hughesYoungEquation84PositiveContourSeries
  dsimp only
  apply tsum_congr
  intro q
  exact hughesYoungEquation84Positive_summand_eq_contourTerm
    T t u hcHalf h k a b hr q

/-- Exact negative-series entry into the pole-cancelled contour. -/
theorem hughesYoungEquation84Negative_eq_contourSeries
    (T t u : ℝ) {c : ℝ} (hcHalf : c < 1 / 2)
    (h k a b : ℕ) {r : ℕ} (hr : 0 < r) :
    hughesYoungEquation84Negative T t c u h k a b r =
      hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((c : ℂ) + (u : ℂ) * I) := by
  unfold hughesYoungEquation84Negative
    hughesYoungEquation84NegativeContourSeries
  dsimp only
  apply tsum_congr
  intro q
  exact hughesYoungEquation84Negative_summand_eq_contourTerm
    T t u hcHalf h k a b hr q

/-- The reduced static Mellin factor is entire in the contour variable. -/
theorem differentiableAt_hughesYoungReducedMellinStaticComplex
    (T t : ℝ) (h k : ℕ) (w : ℂ) :
    DifferentiableAt ℂ
      (hughesYoungReducedMellinStaticComplex T t h k) w := by
  unfold hughesYoungReducedMellinStaticComplex
  fun_prop

/-- The logarithmic positive-shift power is entire in `w`. -/
theorem differentiableAt_hughesYoungCentralShiftPower
    (r : ℕ) (w : ℂ) :
    DifferentiableAt ℂ (hughesYoungCentralShiftPower r) w := by
  unfold hughesYoungCentralShiftPower
  fun_prop

/-- Every positive equation-(84) summand is holomorphic throughout the
rectangle used by Hughes--Young. -/
theorem differentiableAt_hughesYoungEquation84PositiveContourTerm
    (T t : ℝ) (h k a b r q : ℕ) {w : ℂ}
    (hw : 0 < w.re) (hwUpper : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (hughesYoungEquation84PositiveContourTerm T t h k a b r q) w := by
  unfold hughesYoungEquation84PositiveContourTerm
  exact (differentiableAt_const _).mul
    ((differentiableAt_hughesYoungReducedMellinStaticComplex T t h k w).mul
      (differentiableAt_hughesYoungCentralShiftPower r w) |>.mul
        (differentiableAt_hughesYoungEquation84RegularizedContourKernel
          t hw hwUpper))

/-- Every negative equation-(84) summand is holomorphic on the same
rectangle. -/
theorem differentiableAt_hughesYoungEquation84NegativeContourTerm
    (T t : ℝ) (h k a b r q : ℕ) {w : ℂ}
    (hw : 0 < w.re) (hwUpper : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (hughesYoungEquation84NegativeContourTerm T t h k a b r q) w := by
  unfold hughesYoungEquation84NegativeContourTerm
  exact (differentiableAt_const _).mul
    ((differentiableAt_hughesYoungReducedMellinStaticComplex T t h k w).mul
      (differentiableAt_hughesYoungCentralShiftPower r w) |>.mul
        (differentiableAt_hughesYoungEquation84RegularizedContourKernel
          (-t) hw hwUpper))

/-- Holomorphy of one positive central summand on a closed rectangle inside
`0 < Re w < 3/2`. -/
theorem differentiableOn_hughesYoungEquation84PositiveContourTerm_rectangle
    (T t : ℝ) (h k a b r q : ℕ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ < 3 / 2) :
    DifferentiableOn ℂ
      (hughesYoungEquation84PositiveContourTerm T t h k a b r q)
      ([[c₀, c₁]] ×ℂ [[-H, H]]) := by
  intro w hw
  rw [mem_reProdIm] at hw
  have hwre₀ : c₀ ≤ w.re := by
    rw [uIcc_of_le hc] at hw
    exact hw.1.1
  have hwre₁ : w.re ≤ c₁ := by
    rw [uIcc_of_le hc] at hw
    exact hw.1.2
  exact (differentiableAt_hughesYoungEquation84PositiveContourTerm
    T t h k a b r q (hc₀.trans_le hwre₀) (hwre₁.trans_lt hc₁)).differentiableWithinAt

/-- Holomorphy of one negative central summand on the same rectangle. -/
theorem differentiableOn_hughesYoungEquation84NegativeContourTerm_rectangle
    (T t : ℝ) (h k a b r q : ℕ)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁)
    (hc₁ : c₁ < 3 / 2) :
    DifferentiableOn ℂ
      (hughesYoungEquation84NegativeContourTerm T t h k a b r q)
      ([[c₀, c₁]] ×ℂ [[-H, H]]) := by
  intro w hw
  rw [mem_reProdIm] at hw
  have hwre₀ : c₀ ≤ w.re := by
    rw [uIcc_of_le hc] at hw
    exact hw.1.1
  have hwre₁ : w.re ≤ c₁ := by
    rw [uIcc_of_le hc] at hw
    exact hw.1.2
  exact (differentiableAt_hughesYoungEquation84NegativeContourTerm
    T t h k a b r q (hc₀.trans_le hwre₀) (hwre₁.trans_lt hc₁)).differentiableWithinAt

/-- Exact finite-height positive central contour shift. -/
theorem hughesYoungEquation84PositiveContourTerm_boundaryRect_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ H : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ < 3 / 2) :
    (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84PositiveContourTerm T t h k a b r q
          ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84PositiveContourTerm T t h k a b r q
          ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84PositiveContourTerm T t h k a b r q
          ((c₁ : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84PositiveContourTerm T t h k a b r q
          ((c₀ : ℂ) + (y : ℂ) * I)) = 0 := by
  have hdiff :=
    differentiableOn_hughesYoungEquation84PositiveContourTerm_rectangle
      T t h k a b r q hc₀ hc hc₁ (H := H)
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (hughesYoungEquation84PositiveContourTerm T t h k a b r q)
    ((c₀ : ℂ) - (H : ℂ) * I) ((c₁ : ℂ) + (H : ℂ) * I) (by
      simpa using hdiff)
  simpa using hrect

/-- Exact finite-height negative central contour shift. -/
theorem hughesYoungEquation84NegativeContourTerm_boundaryRect_zero
    (T t : ℝ) (h k a b r q : ℕ) {c₀ c₁ H : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ < 3 / 2) :
    (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84NegativeContourTerm T t h k a b r q
          ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84NegativeContourTerm T t h k a b r q
          ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84NegativeContourTerm T t h k a b r q
          ((c₁ : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84NegativeContourTerm T t h k a b r q
          ((c₀ : ℂ) + (y : ℂ) * I)) = 0 := by
  have hdiff :=
    differentiableOn_hughesYoungEquation84NegativeContourTerm_rectangle
      T t h k a b r q hc₀ hc hc₁ (H := H)
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (hughesYoungEquation84NegativeContourTerm T t h k a b r q)
    ((c₀ : ℂ) - (H : ℂ) * I) ((c₁ : ℂ) + (H : ℂ) * I) (by
      simpa using hdiff)
  simpa using hrect

end RiemannZeta.GuthMaynard
