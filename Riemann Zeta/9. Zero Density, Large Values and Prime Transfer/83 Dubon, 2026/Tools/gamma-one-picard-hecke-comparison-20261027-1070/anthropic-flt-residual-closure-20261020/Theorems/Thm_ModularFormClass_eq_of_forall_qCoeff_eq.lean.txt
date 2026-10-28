import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularFormClass_eq_of_forall_qCoeff_eq

theorem ModularFormClass.eq_of_forall_qCoeff_eq {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by p2m_exact_reverting @_root_.P2MW.S_ModularFormClass_eq_of_forall_qCoeff_eq.solution
