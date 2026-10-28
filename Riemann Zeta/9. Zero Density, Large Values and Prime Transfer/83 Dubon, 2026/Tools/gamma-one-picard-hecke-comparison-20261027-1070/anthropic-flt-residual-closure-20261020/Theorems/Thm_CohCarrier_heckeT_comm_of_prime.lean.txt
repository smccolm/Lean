import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_comm_of_prime
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.heckeT_comm_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (heckeT M H ℓ' V F) = heckeT M H ℓ' V (heckeT M H ℓ V F) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_comm_of_prime.solution
