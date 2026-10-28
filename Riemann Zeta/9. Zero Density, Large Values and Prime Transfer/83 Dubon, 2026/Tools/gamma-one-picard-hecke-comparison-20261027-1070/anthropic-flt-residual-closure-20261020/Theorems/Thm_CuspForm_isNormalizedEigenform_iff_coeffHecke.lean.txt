import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_isNormalizedEigenform_iff_coeffHecke

theorem CuspForm.isNormalizedEigenform_iff_coeffHecke {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime → ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧ (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n))) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isNormalizedEigenform_iff_coeffHecke.solution
