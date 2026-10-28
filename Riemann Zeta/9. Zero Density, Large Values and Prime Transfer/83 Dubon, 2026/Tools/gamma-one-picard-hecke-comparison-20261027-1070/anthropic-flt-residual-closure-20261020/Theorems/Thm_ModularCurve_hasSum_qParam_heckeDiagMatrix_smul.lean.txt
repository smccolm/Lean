import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul

theorem ModularCurve.hasSum_qParam_heckeDiagMatrix_smul (ℓ : ℕ) [NeZero ℓ] (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (ModularCurve.qExpand ℂ (ℓ * ℓ) A).coeff m * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeDiagMatrix ℓ • τ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.solution
