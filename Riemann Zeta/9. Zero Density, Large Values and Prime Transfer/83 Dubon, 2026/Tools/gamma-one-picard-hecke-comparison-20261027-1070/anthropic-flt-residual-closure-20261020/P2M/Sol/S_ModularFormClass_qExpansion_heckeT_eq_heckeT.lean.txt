import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import P2M.Util
namespace P2MW.S_ModularFormClass_qExpansion_heckeT_eq_heckeT

theorem solution {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℕ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (hk : 1 ≤ k) :
    UpperHalfPlane.qExpansion 1 (ModularForm.heckeT k p ⇑f)
      = PowerSeries.heckeT p k (UpperHalfPlane.qExpansion 1 ⇑f) := by
  ext n
  have h := ModularFormClass.qCoeff_heckeT (k := (k : ℤ)) f hΓ hp n
  simp only [ModularFormClass.qCoeff] at h
  rw [PowerSeries.coeff_heckeT, h, ModularForm.coeffHeckeT, mul_comm n p]
  have hk' : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [hk', zpow_natCast]
  split_ifs <;> simp [ModularFormClass.qCoeff]
