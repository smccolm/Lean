import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral

open Complex in

theorem Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (P Q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        (P (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) +
          Q (c + r φ * exp (φ * I)) *
            (starRingEnd ℂ) ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I))) =
      2 * I * ∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))},
        ((fderiv ℝ P z 1 + I * fderiv ℝ P z I) / 2 - (fderiv ℝ Q z 1 - I * fderiv ℝ Q z I) / 2) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral.solution
