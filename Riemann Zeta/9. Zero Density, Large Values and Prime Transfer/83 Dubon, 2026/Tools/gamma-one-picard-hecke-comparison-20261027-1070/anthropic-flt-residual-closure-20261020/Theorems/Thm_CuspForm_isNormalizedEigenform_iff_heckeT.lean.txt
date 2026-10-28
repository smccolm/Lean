import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_isNormalizedEigenform_iff_heckeT

theorem CuspForm.isNormalizedEigenform_iff_heckeT {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime → ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧ (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isNormalizedEigenform_iff_heckeT.solution
