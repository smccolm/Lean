import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries
import P2M.Util
import P2M.Sol.S_ModularCurve_laurent_qParam_coeff_unique

theorem ModularCurve.laurent_qParam_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (A B : LaurentSeries ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => B.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : A = B := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurent_qParam_coeff_unique.solution
