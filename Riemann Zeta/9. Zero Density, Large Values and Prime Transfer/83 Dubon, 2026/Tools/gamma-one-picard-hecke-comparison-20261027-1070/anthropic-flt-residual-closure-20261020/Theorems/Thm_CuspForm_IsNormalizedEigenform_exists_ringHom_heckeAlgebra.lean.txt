import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra

theorem CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (S : Set ℕ) : ∃ χ : CuspForm.heckeAlgebra N 2 S →+* ℂ, (∀ t : CuspForm.heckeAlgebra N 2 S, (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = χ t • f) ∧ (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = ModularFormClass.qCoeff f ℓ) ∧ ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S), χ (CuspForm.heckeAlgebra.U hq hqN hqS) = ModularFormClass.qCoeff f q := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra.solution
