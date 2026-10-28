import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.PowerSeries.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_qParam_mul

theorem ModularCurve.hasSum_qParam_mul (h : ℝ) (hh : 0 < h) (A B : PowerSeries ℂ) (F G : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m B * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℕ => PowerSeries.coeff m (A * B) * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_qParam_mul.solution
