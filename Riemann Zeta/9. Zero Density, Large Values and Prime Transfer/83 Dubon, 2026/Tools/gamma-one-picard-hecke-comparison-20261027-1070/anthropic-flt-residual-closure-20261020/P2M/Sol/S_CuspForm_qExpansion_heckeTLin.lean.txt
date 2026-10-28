import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT
import P2M.Util
namespace P2MW.S_CuspForm_qExpansion_heckeTLin

theorem solution {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    UpperHalfPlane.qExpansion 1 ⇑(CuspForm.heckeTLin 2 hp hpN f)
      = PowerSeries.heckeT p 2 (UpperHalfPlane.qExpansion 1 ⇑f) := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  rw [CuspForm.coe_heckeTLin_apply]
  exact ModularFormClass.qExpansion_heckeT_eq_heckeT (k := 2) f hΓ hp.ne_zero (by norm_num)
