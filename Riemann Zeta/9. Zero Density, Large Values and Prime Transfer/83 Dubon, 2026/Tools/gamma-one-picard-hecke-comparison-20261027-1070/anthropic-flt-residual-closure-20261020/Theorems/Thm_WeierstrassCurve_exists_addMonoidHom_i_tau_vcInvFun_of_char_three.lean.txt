import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three
    {K : Type*} [Field K] [DecidableEq K] [CharP K 3] (i : Kˣ) (hi : (i : K) ^ 2 = -1) :
    ∃ α β : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
        (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
      (∀ T, HEq (Point.vcInvFun (⟨i, 0, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (α T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, 1, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (β T)) ∧
      (∀ T, α (α T) = -T) ∧ (∀ T, β (β T) + β T + T = 0) ∧ (∀ T, α (β T) = β (β (α T))) ∧
      (∀ γ : VariableChange K,
          γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ →
        ∃ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) ∧
          ((∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) ∨
            (∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T)
              (-(m T))))) ∧
      (∀ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) →
        ∃ γ : VariableChange K, γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ ∧
          ∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.solution
