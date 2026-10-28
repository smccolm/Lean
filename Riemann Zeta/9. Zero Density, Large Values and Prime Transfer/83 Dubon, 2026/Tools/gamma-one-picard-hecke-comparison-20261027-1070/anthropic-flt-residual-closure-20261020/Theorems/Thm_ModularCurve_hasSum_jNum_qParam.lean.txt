import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_jNum_qParam

theorem ModularCurve.hasSum_jNum_qParam (τ : UpperHalfPlane) : HasSum (fun m : ℕ => ((PowerSeries.coeff m ModularCurve.jNum : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (Function.Periodic.qParam 1 (τ : ℂ) * (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_jNum_qParam.solution
