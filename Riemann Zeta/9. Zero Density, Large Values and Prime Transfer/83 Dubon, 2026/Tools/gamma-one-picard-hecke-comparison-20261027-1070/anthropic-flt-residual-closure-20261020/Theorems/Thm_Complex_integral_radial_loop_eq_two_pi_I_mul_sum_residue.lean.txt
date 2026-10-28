import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue

open Complex in

theorem Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (f : ℂ → ℂ) (P : Finset ℂ) (res : ℂ → ℂ)
    (hint : ∀ p ∈ P, ‖p - c‖ < r (arg (p - c)))
    (han : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∉ P → AnalyticAt ℂ f z)
    (hpole : ∀ p ∈ P, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ∀ᶠ z in nhdsWithin p {p}ᶜ, f z = res p / (z - p) + g z) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        f (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) =
      2 * Real.pi * I * ∑ p ∈ P, res p := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_radial_loop_eq_two_pi_I_mul_sum_residue.solution
