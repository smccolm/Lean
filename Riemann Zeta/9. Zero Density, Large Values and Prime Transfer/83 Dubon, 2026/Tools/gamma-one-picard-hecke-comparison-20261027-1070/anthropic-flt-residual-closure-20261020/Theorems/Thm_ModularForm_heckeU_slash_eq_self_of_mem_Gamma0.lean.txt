import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0

theorem ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) : SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.solution
