import Definitions.Def_ModularCurve_PeriodMapBundled
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Theorems.Thm_ModularCurve_periodMap_add
import Theorems.Thm_ModularCurve_periodMap_smul
import P2M.Util
namespace P2MW.S_ModularCurve_periodMap_injective

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve ModularCurve.Period CongruenceSubgroup in

theorem solution {N : ℕ} [NeZero N] :
    Function.Injective (ModularCurve.periodMap N) := by
  intro f g hfg
  by_contra hne
  have hsub : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hzero : periodMap N (f - g) = 0 := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ g, periodMap_add, periodMap_smul, hfg, neg_one_smul, add_neg_cancel]
  obtain ⟨F, hFf, -, hFe, -⟩ := Period.CuspForm.exists_equivariantPrimitive_gamma0 (f - g)
  exact Period.CuspForm.periodHom_ne_zero_of_ne_zero hsub hFe hFf ((periodMap_eq_periodHom hFe hFf).symm.trans hzero)

#print axioms solution
