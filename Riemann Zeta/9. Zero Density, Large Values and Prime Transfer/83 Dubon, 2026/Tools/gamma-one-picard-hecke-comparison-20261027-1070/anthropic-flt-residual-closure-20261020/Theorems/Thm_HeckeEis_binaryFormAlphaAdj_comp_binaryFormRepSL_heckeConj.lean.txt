import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj (K : Type*) [CommRing K] (n N ℓ : ℕ) [NeZero ℓ]
    (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    HeckeEis.binaryFormAlphaAdj K n ℓ ∘ₗ ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.heckeConj N ℓ u)
      = ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (u : CongruenceSubgroup.Gamma0 N)
          ∘ₗ HeckeEis.binaryFormAlphaAdj K n ℓ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj.solution
