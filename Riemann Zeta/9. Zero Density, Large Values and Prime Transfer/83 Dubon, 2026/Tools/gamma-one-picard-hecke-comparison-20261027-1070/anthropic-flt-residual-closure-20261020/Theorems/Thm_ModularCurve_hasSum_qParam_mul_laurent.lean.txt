import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_qParam_mul_laurent

theorem ModularCurve.hasSum_qParam_mul_laurent (h : ℝ) (hh : 0 < h) (A B : LaurentSeries ℂ) (F G : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => B.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (A * B).coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_qParam_mul_laurent.solution
