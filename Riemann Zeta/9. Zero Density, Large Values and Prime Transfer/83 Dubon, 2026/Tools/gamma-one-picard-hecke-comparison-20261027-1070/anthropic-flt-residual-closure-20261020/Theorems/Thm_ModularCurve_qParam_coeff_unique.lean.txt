import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_qParam_coeff_unique

theorem ModularCurve.qParam_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c d : ℕ → ℂ) (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hd : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => d m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : c = d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qParam_coeff_unique.solution
