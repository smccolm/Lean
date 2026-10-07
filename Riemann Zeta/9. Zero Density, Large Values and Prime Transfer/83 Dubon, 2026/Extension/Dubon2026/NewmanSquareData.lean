import Dubon2026.NewmanLaplace
import Dubon2026.RankinSelbergInputBridge

/-! # The genuine exponential-scale coefficient square mean and its bounded error -/

namespace Dubon2026

open Complex Set MeasureTheory Filter Asymptotics
open scoped Topology

noncomputable section

/-- The actual positive-index coefficient square mean on logarithmic scale. -/
def newmanSquareMean (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  (squareSummatory a (Real.exp t) : ℂ) / (Real.exp t : ℂ)

/-- The actual centered coefficient square mean on logarithmic scale. -/
def newmanSquareError (a : ℕ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  newmanSquareMean a t - c

/-- The genuine square mean is measurable, including every jump at an integer cutoff. -/
theorem measurable_newmanSquareMean (a : ℕ → ℂ) : Measurable (newmanSquareMean a) := by
  unfold newmanSquareMean
  exact (Complex.measurable_ofReal.comp ((squareSummatory_mono a).measurable.comp
    Real.continuous_exp.measurable)).div (Complex.measurable_ofReal.comp Real.continuous_exp.measurable)

/-- Centering preserves measurability of the literal summatory error. -/
theorem measurable_newmanSquareError (a : ℕ → ℂ) (c : ℝ) : Measurable (newmanSquareError a c) :=
  (measurable_newmanSquareMean a).sub measurable_const

/-- A proved integer square-sum bound extends to every nonnegative real cutoff. -/
theorem squareSummatory_le_linear {a : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ B * N)
    {x : ℝ} (hx : 0 ≤ x) : squareSummatory a x ≤ B * x :=
  (hb ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hB)

/-- The actual square mean is bounded on the complete real logarithmic scale. -/
theorem norm_newmanSquareMean_le {a : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ B * N) (t : ℝ) :
    ‖newmanSquareMean a t‖ ≤ B := by
  simp only [newmanSquareMean, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (squareSummatory_nonneg a _), abs_of_pos (Real.exp_pos t)]
  exact (div_le_iff₀ (Real.exp_pos t)).mpr (squareSummatory_le_linear hB hb (Real.exp_pos t).le)

/-- The actual centered error is bounded without a rate assumption on its mean. -/
theorem norm_newmanSquareError_le {a : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ B * N) (c t : ℝ) :
    ‖newmanSquareError a c t‖ ≤ B + |c| := by
  exact (norm_sub_le _ _).trans (add_le_add (norm_newmanSquareMean_le hB hb t) (by simp))

/-- The same actual bound supplies the linear Big-O hypothesis in the library's Dirichlet-series integral formula. -/
theorem square_sum_isBigO_linear {a : ℕ → ℂ} {B : ℝ}
    (hb : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ B * N) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨B, .of_forall (fun N => ?_)⟩
  simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun n _ => sq_nonneg ‖a n‖)),
    abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using hb N

end
end Dubon2026
