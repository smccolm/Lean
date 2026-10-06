import Dubon2026.CircleMoments
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Termwise integration of the two exponential series on the actual circle -/

namespace Dubon2026

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem circle_fourier_pow (k : ℤ) (n : ℕ) (z : UnitAddCircle) :
    fourier k z ^ n = fourier ((n : ℤ) * k) z := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ, hn, ← fourier_add]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- The genuine product of the two exponential-series terms. -/
def circleDoubleTerm (c : ℂ) (p : ℕ × ℕ) (z : UnitAddCircle) : ℂ :=
  ((c * fourier 1 z) ^ p.1 / (p.1.factorial : ℂ)) *
    ((c * fourier (-1) z) ^ p.2 / (p.2.factorial : ℂ))

theorem norm_circleDoubleTerm (c : ℂ) (p : ℕ × ℕ) (z : UnitAddCircle) :
    ‖circleDoubleTerm c p z‖ =
      (‖c‖ ^ p.1 / (p.1.factorial : ℝ)) * (‖c‖ ^ p.2 / (p.2.factorial : ℝ)) := by
  simp only [circleDoubleTerm, norm_mul, norm_div, norm_pow, fourier_apply,
    Circle.norm_coe, mul_one, Complex.norm_natCast]

theorem circleDoubleTerm_fourier (c : ℂ) (p : ℕ × ℕ) (z : UnitAddCircle) :
    circleDoubleTerm c p z =
      (c ^ (p.1 + p.2) / ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))) *
        fourier ((p.1 : ℤ) - (p.2 : ℤ)) z := by
  simp only [circleDoubleTerm, mul_pow, circle_fourier_pow, mul_one, mul_neg_one]
  rw [show (p.1 : ℤ) - (p.2 : ℤ) = (p.1 : ℤ) + -(p.2 : ℤ) by ring,
    fourier_add, pow_add]
  ring

theorem integrable_circleDoubleTerm (c : ℂ) (p : ℕ × ℕ) :
    Integrable (circleDoubleTerm c p) AddCircle.haarAddCircle :=
  (by unfold circleDoubleTerm; fun_prop : Continuous (circleDoubleTerm c p)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_circleDoubleTerm (c : ℂ) (p : ℕ × ℕ) :
    (∫ z : UnitAddCircle, circleDoubleTerm c p z ∂AddCircle.haarAddCircle) =
      if p.1 = p.2 then c ^ (2 * p.1) / (p.1.factorial : ℂ) ^ 2 else 0 := by
  simp_rw [circleDoubleTerm_fourier]
  rw [integral_const_mul, integral_circle_fourier]
  by_cases he : p.1 = p.2
  · simp [he, two_mul, pow_two]
  · simp [he, sub_eq_zero]

theorem summable_integral_norm_circleDoubleTerm (c : ℂ) :
    Summable (fun p : ℕ × ℕ =>
      ∫ z : UnitAddCircle, ‖circleDoubleTerm c p z‖ ∂AddCircle.haarAddCircle) := by
  simp_rw [norm_circleDoubleTerm]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact (Real.summable_pow_div_factorial ‖c‖).mul_of_nonneg
    (Real.summable_pow_div_factorial ‖c‖) (fun n => by positivity) (fun n => by positivity)

theorem hasSum_complex_exp_series (w : ℂ) :
    HasSum (fun n : ℕ => w ^ n / (n.factorial : ℂ)) (Complex.exp w) := by
  simpa only [← Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w

theorem hasSum_complex_exp_product_series (v w : ℂ) :
    HasSum (fun p : ℕ × ℕ => (v ^ p.1 / (p.1.factorial : ℂ)) *
      (w ^ p.2 / (p.2.factorial : ℂ))) (Complex.exp (v + w)) := by
  rw [Complex.exp_add]
  apply HasSum.mul (f := fun n : ℕ => v ^ n / (n.factorial : ℂ))
    (g := fun n : ℕ => w ^ n / (n.factorial : ℂ))
    (hasSum_complex_exp_series v) (hasSum_complex_exp_series w)
  exact summable_mul_of_summable_norm (f := fun n : ℕ => v ^ n / (n.factorial : ℂ))
    (g := fun n : ℕ => w ^ n / (n.factorial : ℂ))
    (NormedSpace.norm_expSeries_div_summable v) (NormedSpace.norm_expSeries_div_summable w)

theorem hasSum_circleDoubleTerm (c : ℂ) (z : UnitAddCircle) :
    HasSum (fun p : ℕ × ℕ => circleDoubleTerm c p z)
      (Complex.exp (c * fourier 1 z + c * fourier (-1) z)) :=
  hasSum_complex_exp_product_series _ _

theorem hasSum_circle_integral_diagonal (c : ℂ) :
    HasSum (fun n : ℕ => c ^ (2 * n) / (n.factorial : ℂ) ^ 2)
      (∫ z : UnitAddCircle, Complex.exp (c * fourier 1 z + c * fourier (-1) z)
        ∂AddCircle.haarAddCircle) := by
  have hh := hasSum_integral_of_summable_integral_norm
    (integrable_circleDoubleTerm c) (summable_integral_norm_circleDoubleTerm c)
  simp_rw [(hasSum_circleDoubleTerm c _).tsum_eq, integral_circleDoubleTerm] at hh
  apply hh.prod_fiberwise
  intro n
  simpa only [eq_comm] using hasSum_ite_eq n (c ^ (2 * n) / (n.factorial : ℂ) ^ 2)

end

end Dubon2026
