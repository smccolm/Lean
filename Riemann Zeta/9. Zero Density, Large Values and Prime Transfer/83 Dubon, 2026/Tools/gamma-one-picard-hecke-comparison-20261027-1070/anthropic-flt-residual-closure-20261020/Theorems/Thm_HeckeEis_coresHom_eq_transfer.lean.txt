import Definitions.Def_Gamma0HeckeOperatorHom
import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_HeckeEis_coresHom_eq_transfer

set_option autoImplicit false

theorem HeckeEis.coresHom_eq_transfer {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [AddCommGroup A] (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coresHom_eq_transfer.solution
