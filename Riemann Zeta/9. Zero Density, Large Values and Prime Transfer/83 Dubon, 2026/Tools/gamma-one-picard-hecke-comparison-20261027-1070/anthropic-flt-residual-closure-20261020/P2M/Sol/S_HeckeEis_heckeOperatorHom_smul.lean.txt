import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
namespace P2MW.S_HeckeEis_heckeOperatorHom_smul

open CongruenceSubgroup Subgroup

theorem solution (N ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    {R : Type*} [Monoid R] [DistribMulAction R A] (r : R)
    (φ : Additive ↥(Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (r • φ) =
      r • HeckeEis.heckeOperatorHom N ℓ A φ := by
  ext g
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  show (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, (r • φ) _) =
    r • (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, φ _)
  simp only [AddMonoidHom.smul_apply]
  exact Finset.smul_sum.symm
