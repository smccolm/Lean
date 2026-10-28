import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import P2M.Util
import P2M.Sol.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic

open UpperHalfPlane
open scoped MatrixGroups Pointwise
theorem ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M) (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods) (h : ((M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ) : ℕ∞) < (qExpansion M f).order) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.solution
