import TaoTrudgianYang2025.FiniteSmoothThirdDerivative
import TaoTrudgianYang2025.RobertSargosCubicPhase

/-! Third-derivative test for the actual symmetric phase under local C4 hypotheses. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem hasDerivAt_robertSargos_symmetric_jet
    {f : ℝ → ℝ} {x h : ℝ} {j : ℕ} (hj : j < 4)
    (hp : ContDiffAt ℝ 4 f (x+h)) (hm : ContDiffAt ℝ 4 f (x-h)) :
    HasDerivAt (fun y => robertSargosSymmetricDifference (iteratedDeriv j f) y h)
      (robertSargosSymmetricDifference (iteratedDeriv (j+1) f) x h) x := by
  have hdp := (hasDerivAt_iteratedDeriv_finite hj hp).comp x
    ((hasDerivAt_id x).add_const h)
  have hdm := (hasDerivAt_iteratedDeriv_finite hj hm).comp x
    ((hasDerivAt_id x).sub_const h)
  simpa only [robertSargosSymmetricDifference,mul_one] using hdp.sub hdm

theorem robertSargos_symmetric_third_curvature
    {f : ℝ → ℝ} {a b x h C lam : ℝ} (hh : 0 ≤ h)
    (hx : a ≤ x-h) (hxb : x+h ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc a b, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc a b, iteratedDeriv 4 f y ≤ C*lam) :
    2*h*lam ≤ robertSargosSymmetricDifference (iteratedDeriv 3 f) x h ∧
      robertSargosSymmetricDifference (iteratedDeriv 3 f) x h ≤ C*(2*h*lam) := by
  have hin (y : ℝ) (hy : y ∈ Icc (x-h) (x+h)) : y ∈ Icc a b :=
    ⟨hx.trans hy.1,hy.2.trans hxb⟩
  have hb := derivative_increment_bounds (iteratedDeriv 3 f) (iteratedDeriv 4 f)
    (show x-h ≤ x+h by linarith)
    (fun y hy => hasDerivAt_iteratedDeriv_finite (by norm_num : 3 < 4) (hf y (hin y hy)))
    (fun y hy => hlo y (hin y hy)) (fun y hy => hhi y (hin y hy))
  rw [show (x+h)-(x-h) = 2*h by ring] at hb
  simpa only [robertSargosSymmetricDifference,mul_assoc,mul_comm,mul_left_comm] using hb

theorem robertSargos_symmetric_third_derivative_prefix
    (f : ℝ → ℝ) (A : ℝ) (N : ℕ) {a b h C lam : ℝ}
    (hC : 1 ≤ C) (hh : 0 < h) (hlam : 0 < lam) (hscale : 2*h*lam ≤ 1)
    (ha : a ≤ A-h) (hb : A+N+h ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc a b, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc a b, iteratedDeriv 4 f y ≤ C*lam) :
    ‖∑ n ∈ Finset.range N,
      fordAdditiveCharacter (robertSargosSymmetricDifference f (A+n) h)‖ ≤
        20*C*((N:ℝ)*(2*h*lam)^((1:ℝ)/6)+
          Real.sqrt N*(2*h*lam)^(-(1:ℝ)/6)) := by
  have hin (x : ℝ) (hx : x ∈ Icc A (A+N)) :
      x-h ∈ Icc a b ∧ x+h ∈ Icc a b := by
    constructor <;> constructor <;> linarith [hx.1,hx.2]
  have hj (j : ℕ) (hj : j < 4) (x : ℝ) (hx : x ∈ Icc A (A+N)) :=
    hasDerivAt_robertSargos_symmetric_jet hj (hf (x+h) (hin x hx).2)
      (hf (x-h) (hin x hx).1)
  have hc (x : ℝ) (hx : x ∈ Icc A (A+N)) :=
    robertSargos_symmetric_third_curvature hh.le
      (hin x hx).1.1 (hin x hx).2.2 hf hlo hhi
  exact continuous_third_derivative_bound
    (fun x => robertSargosSymmetricDifference f x h)
    (fun x => robertSargosSymmetricDifference (iteratedDeriv 1 f) x h)
    (fun x => robertSargosSymmetricDifference (iteratedDeriv 2 f) x h)
    (fun x => robertSargosSymmetricDifference (iteratedDeriv 3 f) x h)
    A N hC (by positivity) hscale
    (fun x hx => by simpa only [iteratedDeriv_zero] using hj 0 (by norm_num) x hx)
    (fun x hx => hj 1 (by norm_num) x hx)
    (fun x hx => hj 2 (by norm_num) x hx)
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2)

end TaoTrudgianYang2025
