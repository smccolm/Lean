import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt

open scoped Real

theorem Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
    {R G : ℂ → ℂ} {z₀ t : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ R z)
    (hG : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, R z ≠ t) :
    ∃ Z : Finset ℂ, (∀ a, a ∈ Z ↔ a ∈ Metric.ball z₀ r ∧ R a = t) ∧
      (∮ z in C(z₀, r), G z * deriv R z / (R z - t)) =
        2 * π * Complex.I *
          ∑ a ∈ Z, (analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a := by p2m_exact_reverting @_root_.P2MW.S_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt.solution
