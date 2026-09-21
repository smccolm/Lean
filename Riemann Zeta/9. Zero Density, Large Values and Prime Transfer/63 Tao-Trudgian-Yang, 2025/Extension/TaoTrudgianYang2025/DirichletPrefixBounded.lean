import TaoTrudgianYang2025.DirichletPrefixBlocks
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Uniform boundedness and Gaussian integrability of the finite prefix

These bounds justify the actual whole-line integrals. They are not used
as substitutes for the sharper time mean-square estimate.
-/

noncomputable section

open Complex Filter MeasureTheory
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_dirichletPrefix_le (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dirichletPrefix N a t‖ ≤ ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ := by
  unfold dirichletPrefix
  apply norm_sum_le_of_le
  intro n _
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.neg_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,one_mul,zero_add,sub_zero,
    neg_zero,Real.exp_zero,mul_one]
  exact le_rfl

theorem continuous_dirichletPrefix_reflected (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    Continuous (fun u : ℝ => dirichletPrefix N a (u-t)) :=
  (continuous_dirichletPrefix N a).comp (by fun_prop)

theorem integrable_gaussian_dirichletPrefix_norm_pow
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : ℕ → ℂ) (t : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^k) := by
  let C : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖a n‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hcont : Continuous (fun u : ℝ =>
      Real.exp (-b*u^2)*‖dirichletPrefix N a (u-t)‖^k) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (-b*u^2))).mul
      ((continuous_dirichletPrefix_reflected N a t).norm.pow k)
  apply ((integrable_exp_neg_mul_sq hb).mul_const (C^k)).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletPrefix_le N a (u-t)) k)
    (Real.exp_pos _).le

end TaoTrudgianYang2025
