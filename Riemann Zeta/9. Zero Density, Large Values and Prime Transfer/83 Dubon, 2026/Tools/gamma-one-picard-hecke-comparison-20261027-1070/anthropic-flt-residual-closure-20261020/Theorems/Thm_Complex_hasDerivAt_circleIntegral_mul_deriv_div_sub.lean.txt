import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub

open scoped Real

theorem Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub
    {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀ := by p2m_exact_reverting @_root_.P2MW.S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub.solution
