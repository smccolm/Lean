import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_index_GammaHUpper_of_prime

set_option autoImplicit false

theorem CohCarrier.index_GammaHUpper_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    (GammaHUpper M H ℓ).index = ℓ + 1 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_index_GammaHUpper_of_prime.solution
