import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
namespace P2MW.S_HeckeEis_postcomp_heckeOperatorHom

open CongruenceSubgroup Subgroup

theorem solution (N ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (φ : Additive ↥(Gamma0 N) →+ A) :
    f.comp (HeckeEis.heckeOperatorHom N ℓ A φ) =
      HeckeEis.heckeOperatorHom N ℓ B (f.comp φ) := by
  ext g
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  exact map_sum f _ _
