import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_comp_coeff

set_option autoImplicit false

theorem CohCarrier.heckeT_comp_coeff (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type}
    [AddCommGroup A] [AddCommGroup B] (ℓ : ℕ) [NeZero ℓ] (g : A →+ B) (φ : H1 M H A) :
    heckeT M H ℓ B (g.comp φ) = g.comp (heckeT M H ℓ A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_comp_coeff.solution
