import TaoTrudgianYang2025.RobertSargosZeroRCurvature
import TaoTrudgianYang2025.ContinuousSecondDerivativeRange

/-! Second-derivative test on the genuine positive-q, zero-r mixed phase. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_second_derivative_prefix
    (f : ℝ → ℝ) (A : ℝ) (N : ℕ) {a b h q C lam : ℝ}
    (hC : 0 ≤ C) (hh : 0 < h) (hq : 0 < q) (hlam : 0 < lam)
    (hscale : 2*h*q*lam ≤ 1) (ha : a ≤ A-h) (hb : A+N+q+h ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc a b, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc a b, iteratedDeriv 4 f y ≤ C*lam) :
    ‖∑ n ∈ Finset.range N,
      fordAdditiveCharacter (robertSargosSymmetricDifference f (A+n+q) h-
        robertSargosSymmetricDifference f (A+n) h)‖ ≤
      12*(C*N*Real.sqrt (2*h*q*lam)+2/Real.sqrt (2*h*q*lam)) := by
  have hin (x : ℝ) (hx : x ∈ Icc A (A+N)) :
      x-h ∈ Icc a b ∧ x+h ∈ Icc a b ∧
        x+q-h ∈ Icc a b ∧ x+q+h ∈ Icc a b := by
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    constructor <;> constructor <;> linarith [hx.1,hx.2]
  have hj (j : ℕ) (hj : j < 4) (x : ℝ) (hx : x ∈ Icc A (A+N)) :=
    hasDerivAt_robertSargos_zero_r_jet (f := f) (x := x) (h := h) (q := q) hj
      (hf _ (hin x hx).2.1) (hf _ (hin x hx).1)
      (hf _ (hin x hx).2.2.2) (hf _ (hin x hx).2.2.1)
  have hc (x : ℝ) (hx : x ∈ Icc A (A+N)) :=
    robertSargos_zero_r_second_curvature hh.le hq.le
      (hin x hx).1.1 (hin x hx).2.2.2.2 hf hlo hhi
  exact continuous_second_derivative_range_bound
    (fun x => robertSargosSymmetricDifference f (x+q) h-
      robertSargosSymmetricDifference f x h)
    (fun x => robertSargosSymmetricDifference (iteratedDeriv 1 f) (x+q) h-
      robertSargosSymmetricDifference (iteratedDeriv 1 f) x h)
    (fun x => robertSargosSymmetricDifference (iteratedDeriv 2 f) (x+q) h-
      robertSargosSymmetricDifference (iteratedDeriv 2 f) x h)
    A N hC (by positivity) hscale
    (fun x hx => by simpa only [iteratedDeriv_zero] using hj 0 (by norm_num) x hx)
    (fun x hx => hj 1 (by norm_num) x hx)
    (fun x hx => (hc x hx).1) (fun x hx => (hc x hx).2)

end TaoTrudgianYang2025
