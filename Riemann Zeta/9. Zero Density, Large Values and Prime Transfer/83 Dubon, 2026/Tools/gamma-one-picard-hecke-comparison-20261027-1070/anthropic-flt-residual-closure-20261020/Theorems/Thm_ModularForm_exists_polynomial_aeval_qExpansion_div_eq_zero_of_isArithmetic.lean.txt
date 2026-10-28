import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import P2M.Util
import P2M.Sol.S_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) {k : ℤ} (g h : ModularForm 𝒢 k) (hh : h ≠ 0) : ∃ B : Polynomial (IntermediateField.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ))), B ≠ 0 ∧ B.natDegree ≤ Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∧ Polynomial.aeval (((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) B = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic.solution
