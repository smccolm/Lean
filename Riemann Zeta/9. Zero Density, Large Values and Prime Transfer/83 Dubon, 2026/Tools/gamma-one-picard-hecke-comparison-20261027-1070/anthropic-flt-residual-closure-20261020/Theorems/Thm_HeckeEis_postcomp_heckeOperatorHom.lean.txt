import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_postcomp_heckeOperatorHom

open CongruenceSubgroup Subgroup
theorem HeckeEis.postcomp_heckeOperatorHom (N ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (φ : Additive ↥(Gamma0 N) →+ A) :
    f.comp (HeckeEis.heckeOperatorHom N ℓ A φ) =
      HeckeEis.heckeOperatorHom N ℓ B (f.comp φ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_postcomp_heckeOperatorHom.solution
