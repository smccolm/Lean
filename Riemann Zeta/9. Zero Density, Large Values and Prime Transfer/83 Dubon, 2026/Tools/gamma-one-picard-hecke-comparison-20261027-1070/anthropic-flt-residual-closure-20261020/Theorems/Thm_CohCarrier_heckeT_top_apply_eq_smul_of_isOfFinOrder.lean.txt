import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder

set_option autoImplicit false

theorem CohCarrier.heckeT_top_apply_eq_smul_of_isOfFinOrder
    (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ : CohCarrier.H1 N ⊤ A) (γ : ↥(CohCarrier.GammaH N ⊤)) (hγ : IsOfFinOrder γ) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ)) =
      (ℓ + 1) • φ (Additive.ofMul γ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder.solution
