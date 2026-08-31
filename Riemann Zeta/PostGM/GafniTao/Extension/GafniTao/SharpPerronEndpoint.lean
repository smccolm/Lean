import GafniTao.SharpPerronTermBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integral endpoint of the sharp Perron kernel

At ratio one the kernel is an arctangent, hence has norm at most one half.
This removes the spurious height loss that an absolute-value estimate of the
integrand would introduce at an integral endpoint.
-/

namespace GafniTao

private theorem intervalIntegral_odd_symmetric
    (f : ℝ → ℝ) (T : ℝ) (hodd : ∀ t, f (-t) = -f t) :
    ∫ t in (-T)..T, f t = 0 := by
  have hcomp := intervalIntegral.integral_comp_neg
    (a := -T) (b := T) f
  have hneg :
      (∫ t in (-T)..T, f (-t)) = -∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t)) =
          ∫ t in (-T)..T, -f t := by
            apply intervalIntegral.integral_congr
            intro t _ht
            exact hodd t
      _ = -∫ t in (-T)..T, f t := intervalIntegral.integral_neg
  have heq : -(∫ t in (-T)..T, f t) =
      ∫ t in (-T)..T, f t := by
    rw [← hneg]
    simpa only [neg_neg] using hcomp
  exact eq_zero_of_neg_eq heq

private theorem one_div_vertical_line
    {c t : ℝ} (hc : 0 < c) :
    (1 : ℂ) / ((c : ℂ) + (t : ℂ) * Complex.I) =
      (c / (c ^ 2 + t ^ 2) : ℝ) -
        (t / (c ^ 2 + t ^ 2) : ℝ) * Complex.I := by
  have hden : c ^ 2 + t ^ 2 ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.div_re, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      Complex.add_im, Complex.mul_im, zero_add, Complex.normSq_apply,
      Complex.sub_re, Complex.mul_re]
    field_simp [hden]
    ring
  · simp only [Complex.div_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      Complex.add_im, Complex.mul_im, zero_add, Complex.normSq_apply,
      Complex.sub_im]
    field_simp [hden]
    ring

/-- Exact value of the finite Perron kernel at its discontinuity. -/
theorem sharpPerronRatioKernel_one
    {c T : ℝ} (hc : 0 < c) :
    sharpPerronRatioKernel c T 1 =
      ((Real.arctan (T / c) - Real.arctan (-T / c)) /
        (2 * Real.pi) : ℝ) := by
  have hrealCont : Continuous (fun t : ℝ => c / (c ^ 2 + t ^ 2)) := by
    exact continuous_const.div
      ((continuous_const.pow 2).add (continuous_id.pow 2))
      (fun _ => by positivity)
  have himagCont : Continuous (fun t : ℝ => t / (c ^ 2 + t ^ 2)) := by
    exact continuous_id.div
      ((continuous_const.pow 2).add (continuous_id.pow 2))
      (fun _ => by positivity)
  have himagZero : (∫ t in (-T)..T, t / (c ^ 2 + t ^ 2)) = 0 := by
    apply intervalIntegral_odd_symmetric
    intro t
    ring
  have hrealInt : IntervalIntegrable
      (fun t : ℝ => ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ))
      MeasureTheory.volume (-T) T :=
    (Complex.continuous_ofReal.comp hrealCont).intervalIntegrable _ _
  have himagInt : IntervalIntegrable
      (fun t : ℝ => ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume (-T) T :=
    ((Complex.continuous_ofReal.comp himagCont).mul
      continuous_const).intervalIntegrable _ _
  rw [sharpPerronRatioKernel]
  simp only [Complex.ofReal_one, Complex.one_cpow, one_div]
  have hint :
      (∫ t in (-T)..T,
          ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
        ((Real.arctan (T / c) - Real.arctan (-T / c) : ℝ) : ℂ) := by
    calc
      (∫ t in (-T)..T,
          ((c : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
          ∫ t in (-T)..T,
            ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) -
              ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I := by
                apply intervalIntegral.integral_congr
                intro t _ht
                simpa only [one_div] using one_div_vertical_line (t := t) hc
      _ = (∫ t in (-T)..T,
              ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) -
            ∫ t in (-T)..T,
              ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I := by
                rw [intervalIntegral.integral_sub hrealInt himagInt]
      _ = ((∫ t in (-T)..T, c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) -
            (((∫ t in (-T)..T, t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) *
              Complex.I) := by
                rw [intervalIntegral.integral_ofReal,
                  intervalIntegral.integral_mul_const,
                  intervalIntegral.integral_ofReal]
      _ = ((Real.arctan (T / c) - Real.arctan (-T / c) : ℝ) : ℂ) := by
                rw [integral_div_sq_add_sq, himagZero]
                simp
  rw [hint]
  push_cast
  ring

/-- The discontinuity value has norm at most one half. -/
theorem norm_sharpPerronRatioKernel_one_le_half
    {c T : ℝ} (hc : 0 < c) :
    ‖sharpPerronRatioKernel c T 1‖ ≤ (1 / 2 : ℝ) := by
  rw [sharpPerronRatioKernel_one hc, Complex.norm_real, Real.norm_eq_abs]
  have hupper := Real.arctan_lt_pi_div_two (T / c)
  have hlower := Real.neg_pi_div_two_lt_arctan (-T / c)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hdiffUpper :
      Real.arctan (T / c) - Real.arctan (-T / c) < Real.pi := by
    linarith
  have hdiffLower :
      -Real.pi < Real.arctan (T / c) - Real.arctan (-T / c) := by
    have hupperNeg := Real.arctan_lt_pi_div_two (-T / c)
    have hlowerPos := Real.neg_pi_div_two_lt_arctan (T / c)
    linarith
  rw [abs_le]
  constructor
  · apply le_of_lt
    apply (lt_div_iff₀ hpi).2
    nlinarith
  · apply le_of_lt
    apply (div_lt_iff₀ hpi).2
    nlinarith

/-- Physical endpoint form of the half bound. -/
theorem norm_sharpPerronKernel_at_natCast_le_half
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x)
    (hn : 1 ≤ n) (hxn : x = (n : ℝ)) :
    ‖sharpPerronKernel c T x n‖ ≤ (1 / 2 : ℝ) := by
  rw [sharpPerronKernel_eq_ratioKernel hx hn, hxn]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  rw [div_self hnpos.ne']
  exact norm_sharpPerronRatioKernel_one_le_half hc

/-- Height-uniform endpoint contribution to the von Mangoldt cutoff error. -/
theorem norm_vonMangoldt_mul_sharpPerron_sub_cutoff_le_three_halves_at_natCast
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x)
    (hn : 1 ≤ n) (hxn : x = (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖ ≤
      ArithmeticFunction.vonMangoldt n * (3 / 2 : ℝ) := by
  have hnle : (n : ℝ) ≤ x := hxn.symm.le
  have hcut : sharpPerronCutoff x n = 1 := by
    simp [sharpPerronCutoff, hnle]
  rw [hcut]
  have hfactor :
      (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
          (ArithmeticFunction.vonMangoldt n : ℂ) * 1 =
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (sharpPerronKernel c T x n - 1) := by ring
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  calc
    ‖sharpPerronKernel c T x n - 1‖ ≤
        ‖sharpPerronKernel c T x n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (1 / 2 : ℝ) + 1 := by
      simpa using add_le_add_right
        (norm_sharpPerronKernel_at_natCast_le_half hc hx hn hxn) 1
    _ = 3 / 2 := by norm_num

end GafniTao
