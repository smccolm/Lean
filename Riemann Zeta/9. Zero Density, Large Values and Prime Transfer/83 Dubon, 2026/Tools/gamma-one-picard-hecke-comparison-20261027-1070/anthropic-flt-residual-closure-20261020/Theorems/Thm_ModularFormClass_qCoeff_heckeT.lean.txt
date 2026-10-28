import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularFormClass_qCoeff_heckeT

theorem ModularFormClass.qCoeff_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeT k p f) n = ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n := by p2m_exact_reverting @_root_.P2MW.S_ModularFormClass_qCoeff_heckeT.solution
