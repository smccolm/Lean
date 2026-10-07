import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Argument change along curves confined to a closed half-plane -/

namespace Dubon2026

open MeasureTheory Set

theorem mem_slitPlane_of_re_nonneg {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    by_contra h
    exact hz (Complex.ext (le_antisymm (le_of_not_gt h) hr) hi)
  · exact Or.inr hi

theorem abs_im_integral_logDerivative_le_pi_of_re_nonneg {f f' : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc a b, f x ≠ 0) (hr : ∀ x ∈ Icc a b, 0 ≤ (f x).re)
    (hi : IntervalIntegrable (fun x => f' x / f x) volume a b) :
    |(∫ x in a..b, f' x / f x).im| ≤ Real.pi := by
  have he : (∫ x in a..b, f' x / f x) = Complex.log (f b) - Complex.log (f a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hi
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (hf x hx).clog_real (mem_slitPlane_of_re_nonneg (hn x hx) (hr x hx))
  rw [he, Complex.sub_im, Complex.log_im, Complex.log_im]
  have ha := Complex.abs_arg_le_pi_div_two_iff.mpr (hr a ⟨le_rfl, hab⟩)
  have hb := Complex.abs_arg_le_pi_div_two_iff.mpr (hr b ⟨hab, le_rfl⟩)
  exact (abs_sub _ _).trans (by linarith)

theorem abs_im_integral_logDerivative_le_pi_of_re_nonpos {f f' : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc a b, f x ≠ 0) (hr : ∀ x ∈ Icc a b, (f x).re ≤ 0)
    (hi : IntervalIntegrable (fun x => f' x / f x) volume a b) :
    |(∫ x in a..b, f' x / f x).im| ≤ Real.pi := by
  have hder : ∀ x ∈ Icc a b, HasDerivAt (fun y => -f y) (-f' x) x :=
    fun x hx => (hf x hx).neg
  have hnon : ∀ x ∈ Icc a b, -f x ≠ 0 := fun x hx => neg_ne_zero.mpr (hn x hx)
  have hpos : ∀ x ∈ Icc a b, 0 ≤ (-f x).re := by
    intro x hx
    simpa only [Complex.neg_re, neg_nonneg] using hr x hx
  simpa only [neg_div_neg_eq] using
    abs_im_integral_logDerivative_le_pi_of_re_nonneg hab hder hnon hpos
      (by simpa only [neg_div_neg_eq] using hi)

end Dubon2026
