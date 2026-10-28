import Definitions.Def_CohCarrier_Level
import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom

open scoped MatrixGroups in

theorem CohCarrier.heckeT_top_apply_eq_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (ψ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A)
    (hφψ : ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      φ (Additive.ofMul γ) =
        ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩))
    (γ : ↥(CohCarrier.GammaH N ⊤)) :
    CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ) =
      HeckeEis.heckeOperatorHom N ℓ A ψ
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom.solution
