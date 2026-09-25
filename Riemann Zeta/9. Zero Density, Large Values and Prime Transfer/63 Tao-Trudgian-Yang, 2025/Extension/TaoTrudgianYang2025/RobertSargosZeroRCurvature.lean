import TaoTrudgianYang2025.RobertSargosSymmetricThirdDerivative

/-! Actual second curvature of the r=0 mixed phase, from the fourth derivative. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem hasDerivAt_robertSargos_zero_r_jet
    {f : ℝ → ℝ} {x h q : ℝ} {j : ℕ} (hj : j < 4)
    (hxp : ContDiffAt ℝ 4 f (x+h)) (hxm : ContDiffAt ℝ 4 f (x-h))
    (hxqp : ContDiffAt ℝ 4 f (x+q+h)) (hxqm : ContDiffAt ℝ 4 f (x+q-h)) :
    HasDerivAt
      (fun y => robertSargosSymmetricDifference (iteratedDeriv j f) (y+q) h-
        robertSargosSymmetricDifference (iteratedDeriv j f) y h)
      (robertSargosSymmetricDifference (iteratedDeriv (j+1) f) (x+q) h-
        robertSargosSymmetricDifference (iteratedDeriv (j+1) f) x h) x :=
  hasDerivAt_shift_difference
    (fun y => robertSargosSymmetricDifference (iteratedDeriv j f) y h)
    (fun y => robertSargosSymmetricDifference (iteratedDeriv (j+1) f) y h)
    (x := x) (h := q)
    (hasDerivAt_robertSargos_symmetric_jet (f := f) (x := x) (h := h) hj hxp hxm)
    (hasDerivAt_robertSargos_symmetric_jet (f := f) (x := x+q) (h := h) hj hxqp hxqm)

theorem robertSargos_zero_r_second_curvature
    {f : ℝ → ℝ} {a b x h q C lam : ℝ} (hh : 0 ≤ h) (hq : 0 ≤ q)
    (hx : a ≤ x-h) (hxb : x+q+h ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc a b, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc a b, iteratedDeriv 4 f y ≤ C*lam) :
    2*h*q*lam ≤
        robertSargosSymmetricDifference (iteratedDeriv 2 f) (x+q) h-
          robertSargosSymmetricDifference (iteratedDeriv 2 f) x h ∧
      robertSargosSymmetricDifference (iteratedDeriv 2 f) (x+q) h-
          robertSargosSymmetricDifference (iteratedDeriv 2 f) x h ≤ C*(2*h*q*lam) := by
  have hin (y : ℝ) (hy : y ∈ Icc x (x+q)) :
      y-h ∈ Icc a b ∧ y+h ∈ Icc a b := by
    constructor <;> constructor <;> linarith [hy.1,hy.2]
  have hd (y : ℝ) (hy : y ∈ Icc x (x+q)) :=
    hasDerivAt_robertSargos_symmetric_jet (by norm_num : 2 < 4)
      (hf (y+h) (hin y hy).2) (hf (y-h) (hin y hy).1)
  have hc (y : ℝ) (hy : y ∈ Icc x (x+q)) :=
    robertSargos_symmetric_third_curvature hh
      (hin y hy).1.1 (hin y hy).2.2 hf hlo hhi
  have hb := derivative_increment_bounds
    (fun y => robertSargosSymmetricDifference (iteratedDeriv 2 f) y h)
    (fun y => robertSargosSymmetricDifference (iteratedDeriv 3 f) y h)
    (show x ≤ x+q by linarith) hd
    (fun y hy => (hc y hy).1) (fun y hy => (hc y hy).2)
  rw [show (x+q)-x = q by ring] at hb
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hb

end TaoTrudgianYang2025
