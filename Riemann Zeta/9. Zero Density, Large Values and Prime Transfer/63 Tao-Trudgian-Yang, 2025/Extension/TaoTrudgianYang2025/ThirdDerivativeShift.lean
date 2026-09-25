import TaoTrudgianYang2025.ContinuousDerivativeBounds

/-! Curvature of genuine shifted differences from a continuous third derivative. -/

noncomputable section
open Set
namespace TaoTrudgianYang2025

theorem third_derivative_shift_curvature
    (F'' F''' : ℝ → ℝ) {a b x h μ Λ : ℝ}
    (hh : 0 ≤ h) (hx : a ≤ x) (hxb : x+h ≤ b)
    (hder : ∀ y ∈ Icc a b, HasDerivAt F'' (F''' y) y)
    (hlo : ∀ y ∈ Icc a b, μ ≤ F''' y)
    (hhi : ∀ y ∈ Icc a b, F''' y ≤ Λ) :
    h*μ ≤ F'' (x+h)-F'' x ∧ F'' (x+h)-F'' x ≤ h*Λ := by
  have hin (y : ℝ) (hy : y ∈ Icc x (x+h)) : y ∈ Icc a b :=
    ⟨hx.trans hy.1,hy.2.trans hxb⟩
  have hb := derivative_increment_bounds F'' F''' (show x ≤ x+h by linarith)
    (fun y hy => hder y (hin y hy))
    (fun y hy => hlo y (hin y hy))
    (fun y hy => hhi y (hin y hy))
  simpa only [add_sub_cancel_left,mul_comm] using hb

theorem hasDerivAt_shift_difference
    (F F' : ℝ → ℝ) {x h : ℝ}
    (hx : HasDerivAt F (F' x) x)
    (hxh : HasDerivAt F (F' (x+h)) (x+h)) :
    HasDerivAt (fun y => F (y+h)-F y) (F' (x+h)-F' x) x := by
  have he := hxh.comp x ((hasDerivAt_id x).add_const h)
  simpa only [mul_one] using he.sub hx

end TaoTrudgianYang2025
