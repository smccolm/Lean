import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_CohCarrier_transfer_restrict_eq_pow_index

set_option autoImplicit false

theorem CohCarrier.transfer_restrict_eq_pow_index {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {C : Type*} [CommGroup C]
    (φ : G →* C) :
    MonoidHom.transfer (φ.domRestrict K) = φ ^ K.index := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_transfer_restrict_eq_pow_index.solution
