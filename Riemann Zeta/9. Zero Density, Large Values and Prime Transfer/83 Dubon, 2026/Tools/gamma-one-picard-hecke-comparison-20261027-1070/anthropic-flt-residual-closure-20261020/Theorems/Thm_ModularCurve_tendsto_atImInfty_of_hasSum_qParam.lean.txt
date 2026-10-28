import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_tendsto_atImInfty_of_hasSum_qParam

theorem ModularCurve.tendsto_atImInfty_of_hasSum_qParam (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c : ℕ → ℂ) (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : Filter.Tendsto F UpperHalfPlane.atImInfty (nhds (c 0)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tendsto_atImInfty_of_hasSum_qParam.solution
