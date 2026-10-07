import Dubon2026.NewmanSquareData
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The actual coefficient square Laplace transform equals its literal Dirichlet series -/

namespace Dubon2026

open Complex Set MeasureTheory Filter Asymptotics
open scoped Topology

noncomputable section

/-- Exponentiation maps the positive integration ray onto the actual Mellin ray. -/
theorem newman_exp_image_Ioi : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact Real.one_lt_exp_iff.mpr ht
  · intro hx
    change 1 < x at hx
    exact ⟨Real.log x, Real.log_pos hx, Real.exp_log (by linarith : 0 < x)⟩

/-- The exponential Jacobian and principal complex power give the exact summatory Laplace integrand. -/
theorem newman_square_mellin_integrand (a : ℕ → ℂ) (z : ℂ) (t : ℝ) :
    |Real.exp t| • ((squareSummatory a (Real.exp t) : ℂ) *
      (Real.exp t : ℂ) ^ (-(z + 1 + 1))) =
        newmanSquareMean a t * Complex.exp (-z * t) := by
  rw [abs_of_pos (Real.exp_pos t), Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)), ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp]
  simp only [newmanSquareMean, Complex.real_smul, Complex.ofReal_exp]
  calc
    _ = (squareSummatory a (Real.exp t) : ℂ) * Complex.exp ((t : ℂ) + t * (-(z + 1 + 1))) := by
      rw [Complex.exp_add]
      ring
    _ = (squareSummatory a (Real.exp t) : ℂ) * Complex.exp (-z * t - t) := by congr 2; ring
    _ = _ := by rw [Complex.exp_sub]; ring

/-- The literal normalized square-mean Laplace integral is the actual square Dirichlet series divided by its Mellin parameter. -/
theorem newmanSquareMean_laplace {a : ℕ → ℂ} {B : ℝ}
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ B * N)
    {z : ℂ} (hz : 0 < z.re) :
    newmanLaplace (newmanSquareMean a) z =
      LSeries (fun n => ((‖a n‖ ^ 2 : ℝ) : ℂ)) (z + 1) / (z + 1) := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0 : ℝ)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun x : ℝ => (squareSummatory a x : ℂ) * (x : ℂ) ^ (-(z + 1 + 1)))
  rw [newman_exp_image_Ioi] at hi
  simp_rw [newman_square_mellin_integrand] at hi
  have hs := LSeries_eq_mul_integral_of_nonneg (fun n => ‖a n‖ ^ 2)
    (by norm_num : (0 : ℝ) ≤ 1) (s := z + 1) (by simpa using hz)
    (square_sum_isBigO_linear hb) (fun n => sq_nonneg _)
  have he : (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((‖a n‖ ^ 2 : ℝ) : ℂ)) *
      (x : ℂ) ^ (-(z + 1 + 1))) =
      (fun x : ℝ => (squareSummatory a x : ℂ) * (x : ℂ) ^ (-(z + 1 + 1))) := by
    funext x
    simp only [squareSummatory, Complex.ofReal_sum]
  rw [he, hi] at hs
  have hz1 : z + 1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  rw [hs, mul_div_cancel_left₀ _ hz1]
  rfl

/-- Centering the actual mean subtracts exactly its constant Laplace pole. -/
theorem newmanSquareError_laplace {a : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ B * N)
    (c : ℝ) {z : ℂ} (hz : 0 < z.re) :
    newmanLaplace (newmanSquareError a c) z =
      LSeries (fun n => ((‖a n‖ ^ 2 : ℝ) : ℂ)) (z + 1) / (z + 1) - (c : ℂ) / z := by
  have hi := newmanLaplace_integrable (measurable_newmanSquareMean a).aestronglyMeasurable
    (fun t _ => norm_newmanSquareMean_le hB hb t) hz
  have hc : IntegrableOn (fun t : ℝ => (c : ℂ) * Complex.exp (-z * t)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (by change -z.re < 0; linarith) 0).const_mul (c : ℂ)
  have he : (fun t : ℝ => newmanSquareError a c t * Complex.exp (-z * t)) =
      (fun t : ℝ => newmanSquareMean a t * Complex.exp (-z * t) - (c : ℂ) * Complex.exp (-z * t)) := by
    funext t
    simp only [newmanSquareError, sub_mul]
  unfold newmanLaplace
  rw [he, integral_sub hi hc, integral_const_mul,
    integral_exp_mul_complex_Ioi (by change -z.re < 0; linarith) 0]
  change newmanLaplace (newmanSquareMean a) z - _ = _
  rw [newmanSquareMean_laplace hb hz]
  simp [div_eq_mul_inv]

end
end Dubon2026
