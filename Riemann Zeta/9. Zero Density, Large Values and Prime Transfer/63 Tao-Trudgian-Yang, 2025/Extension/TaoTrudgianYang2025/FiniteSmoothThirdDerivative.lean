import TaoTrudgianYang2025.ContinuousThirdDerivative
import TaoTrudgianYang2025.FiniteSmoothTaylor

/-! The standard third-derivative estimate from finite local C3 regularity only. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem hasDerivAt_iteratedDeriv_finite
    {F : ℝ → ℝ} {x : ℝ} {n j : ℕ} (hj : j < n)
    (hF : ContDiffAt ℝ n F x) :
    HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j+1) F x) x := by
  have hh : ContDiffAt ℝ (1+j) F x := hF.of_le (by
    exact_mod_cast (show 1+j ≤ n by omega))
  have hd := contDiffAt_iteratedDeriv_finite (n := 1) (j := j) hh
  simpa only [iteratedDeriv_succ] using hd.differentiableAt_one.hasDerivAt

theorem finite_smooth_third_derivative_bound
    (F : ℝ → ℝ) (A : ℝ) (N : ℕ) {C μ : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), ContDiffAt ℝ 3 F x)
    (hlo : ∀ x ∈ Icc A (A+N), μ ≤ iteratedDeriv 3 F x)
    (hhi : ∀ x ∈ Icc A (A+N), iteratedDeriv 3 F x ≤ C*μ) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤
      20*C*((N:ℝ)*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6)) := by
  exact continuous_third_derivative_bound F (iteratedDeriv 1 F)
    (iteratedDeriv 2 F) (iteratedDeriv 3 F) A N hC hμ hμ1
    (fun x hx => by simpa only [iteratedDeriv_zero] using
      hasDerivAt_iteratedDeriv_finite (j := 0) (by norm_num : 0 < 3) (hF x hx))
    (fun x hx => hasDerivAt_iteratedDeriv_finite (by norm_num : 1 < 3) (hF x hx))
    (fun x hx => hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) (hF x hx))
    hlo hhi

theorem finite_smooth_third_derivative_negative_bound
    (F : ℝ → ℝ) (A : ℝ) (N : ℕ) {C μ : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), ContDiffAt ℝ 3 F x)
    (hlo : ∀ x ∈ Icc A (A+N), -(C*μ) ≤ iteratedDeriv 3 F x)
    (hhi : ∀ x ∈ Icc A (A+N), iteratedDeriv 3 F x ≤ -μ) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤
      20*C*((N:ℝ)*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6)) := by
  exact continuous_third_derivative_negative_bound F (iteratedDeriv 1 F)
    (iteratedDeriv 2 F) (iteratedDeriv 3 F) A N hC hμ hμ1
    (fun x hx => by simpa only [iteratedDeriv_zero] using
      hasDerivAt_iteratedDeriv_finite (j := 0) (by norm_num : 0 < 3) (hF x hx))
    (fun x hx => hasDerivAt_iteratedDeriv_finite (by norm_num : 1 < 3) (hF x hx))
    (fun x hx => hasDerivAt_iteratedDeriv_finite (by norm_num : 2 < 3) (hF x hx))
    hlo hhi

end TaoTrudgianYang2025
