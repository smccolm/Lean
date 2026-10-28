import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries.solution
