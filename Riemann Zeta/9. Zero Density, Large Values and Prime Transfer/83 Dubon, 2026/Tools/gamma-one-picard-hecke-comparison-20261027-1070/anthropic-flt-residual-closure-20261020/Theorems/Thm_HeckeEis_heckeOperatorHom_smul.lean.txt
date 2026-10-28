import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_smul

open CongruenceSubgroup Subgroup
theorem HeckeEis.heckeOperatorHom_smul (N ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    {R : Type*} [Monoid R] [DistribMulAction R A] (r : R)
    (φ : Additive ↥(Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (r • φ) =
      r • HeckeEis.heckeOperatorHom N ℓ A φ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_smul.solution
