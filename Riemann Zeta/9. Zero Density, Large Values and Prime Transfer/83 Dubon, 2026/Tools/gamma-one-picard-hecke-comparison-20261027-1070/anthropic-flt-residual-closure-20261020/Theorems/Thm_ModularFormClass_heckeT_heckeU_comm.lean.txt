import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularFormClass_heckeT_heckeU_comm

theorem ModularFormClass.heckeT_heckeU_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p q : ℕ} (hpq : Nat.Coprime p q) : ModularForm.heckeT k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeT k p ⇑f) := by p2m_exact_reverting @_root_.P2MW.S_ModularFormClass_heckeT_heckeU_comm.solution
