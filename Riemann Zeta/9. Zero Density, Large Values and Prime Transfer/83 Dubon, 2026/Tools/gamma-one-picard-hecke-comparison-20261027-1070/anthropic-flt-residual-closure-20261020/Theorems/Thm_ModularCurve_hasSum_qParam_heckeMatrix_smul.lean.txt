import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_qParam_heckeMatrix_smul

theorem ModularCurve.hasSum_qParam_heckeMatrix_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ) (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) * A.coeff m) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeMatrix ℓ b • τ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_qParam_heckeMatrix_smul.solution
