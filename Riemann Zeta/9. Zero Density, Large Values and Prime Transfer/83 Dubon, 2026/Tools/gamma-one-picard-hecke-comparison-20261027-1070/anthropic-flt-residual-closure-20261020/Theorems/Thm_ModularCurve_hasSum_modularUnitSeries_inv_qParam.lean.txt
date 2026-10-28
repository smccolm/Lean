import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam

theorem ModularCurve.hasSum_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) / ModularForm.discriminant τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam.solution
