import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_ModularFormClass_heckeT_eq_smul_iff
import Theorems.Thm_ModularFormClass_heckeU_eq_smul_iff
import P2M.Util
namespace P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeT

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

open ModularForm ModularFormClass

theorem solution {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime → ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧ (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) := by
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N
  rw [CuspForm.isNormalizedEigenform_iff_coeffHecke]
  refine and_congr_right fun _ ↦ forall_congr' fun p ↦ forall_congr' fun hp ↦ ?_
  rw [ModularFormClass.heckeT_eq_smul_iff f hΓ hp.ne_zero, ModularFormClass.heckeU_eq_smul_iff f hΓ hp.ne_zero]

end
