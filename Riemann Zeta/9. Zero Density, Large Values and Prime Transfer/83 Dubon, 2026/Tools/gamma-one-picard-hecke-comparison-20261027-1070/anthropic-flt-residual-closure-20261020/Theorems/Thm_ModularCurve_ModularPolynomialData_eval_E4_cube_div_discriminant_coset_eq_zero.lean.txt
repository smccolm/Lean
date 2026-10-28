import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane

theorem ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) {a b d : ℕ} (habd : (a, b, d) ∈ ModularCurve.primCosetReps N)
    (τ τ' : ℍ) (hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / d) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.solution
