import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq

theorem ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ τ : UpperHalfPlane, ModularForm.heckeDiagMatrix N • γ • τ = γ' • ModularForm.heckeDiagMatrix N • τ) ∧ ∀ τ : UpperHalfPlane, UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ) (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.solution
