import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_mem_coeffCoboundaries (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a)
    {z : CongruenceSubgroup.Gamma0 N → V} (hz : z ∈ HeckeEis.coeffCoboundaries ρ) :
    HeckeEis.coeffHeckeFun N ℓ ρ a z ∈ HeckeEis.coeffCoboundaries ρ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries.solution
