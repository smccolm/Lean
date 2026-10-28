import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularFormClass_heckeU_eq_smul_iff

theorem ModularFormClass.heckeU_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) : ModularForm.heckeU k p ⇑f = c • ⇑f ↔ ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_ModularFormClass_heckeU_eq_smul_iff.solution
