import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.solution
