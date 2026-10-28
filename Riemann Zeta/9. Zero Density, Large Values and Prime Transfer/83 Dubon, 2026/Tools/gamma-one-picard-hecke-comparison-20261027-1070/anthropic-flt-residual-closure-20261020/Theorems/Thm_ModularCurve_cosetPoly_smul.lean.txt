import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_cosetPoly_smul

theorem ModularCurve.cosetPoly_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (F : UpperHalfPlane → ℂ) (hF : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • γ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • γ • τ))) = (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • τ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cosetPoly_smul.solution
