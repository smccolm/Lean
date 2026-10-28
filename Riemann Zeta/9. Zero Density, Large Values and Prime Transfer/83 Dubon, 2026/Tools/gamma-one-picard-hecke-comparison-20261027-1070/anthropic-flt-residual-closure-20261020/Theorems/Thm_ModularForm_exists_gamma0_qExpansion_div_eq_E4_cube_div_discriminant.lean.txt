import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.LaurentSeries
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane
theorem ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant (ℓ : ℕ) [NeZero ℓ] : ∃ G H : ModularForm (CongruenceSubgroup.Gamma0 ℓ) 12, H ≠ 0 ∧ ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant.solution
