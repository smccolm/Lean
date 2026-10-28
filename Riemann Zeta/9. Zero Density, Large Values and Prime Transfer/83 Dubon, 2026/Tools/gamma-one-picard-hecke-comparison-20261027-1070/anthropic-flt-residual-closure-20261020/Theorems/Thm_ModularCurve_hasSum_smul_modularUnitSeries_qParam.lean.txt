import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_smul_modularUnitSeries_qParam

theorem ModularCurve.hasSum_smul_modularUnitSeries_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((((N : ℚ) ^ 12)⁻¹ • ModularCurve.modularUnitSeries N).coeff m : ℚ) : ℂ) * Function.Periodic.qParam N (τ : ℂ) ^ m) (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ) / ModularForm.discriminant (ModularGroup.S • τ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_smul_modularUnitSeries_qParam.solution
