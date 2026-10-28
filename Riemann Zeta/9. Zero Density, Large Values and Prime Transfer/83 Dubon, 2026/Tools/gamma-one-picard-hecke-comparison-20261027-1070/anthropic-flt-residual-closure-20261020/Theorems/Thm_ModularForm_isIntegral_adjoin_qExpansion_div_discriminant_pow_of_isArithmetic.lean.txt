import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import P2M.Util
import P2M.Sol.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (m : ℕ) {k : ℤ} (hk : k = 12 * m) (g : ModularForm 𝒢 k) : IsIntegral (Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ))) (((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.solution
