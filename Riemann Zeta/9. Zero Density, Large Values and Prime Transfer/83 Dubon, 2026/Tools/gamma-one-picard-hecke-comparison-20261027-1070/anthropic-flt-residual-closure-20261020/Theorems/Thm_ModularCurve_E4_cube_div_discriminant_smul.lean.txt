import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Util
import P2M.Sol.S_ModularCurve_E4_cube_div_discriminant_smul

theorem ModularCurve.E4_cube_div_discriminant_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ) = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_E4_cube_div_discriminant_smul.solution
