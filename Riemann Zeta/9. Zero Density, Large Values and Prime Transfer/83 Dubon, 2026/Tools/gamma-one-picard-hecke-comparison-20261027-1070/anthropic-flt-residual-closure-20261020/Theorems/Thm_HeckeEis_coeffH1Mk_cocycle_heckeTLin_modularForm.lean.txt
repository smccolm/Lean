import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm (N : ℕ) [NeZero N] (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N)
    (T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ]
      HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeEis.IsCoeffHeckeOnH1 N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) T)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (F' : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hEI' : HeckeEis.IsEichlerIntegral n (ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f) F')
    (hF' : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F') :
    T (HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩) =
      HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        ⟨hF'.cocycle, hF'.cocycle_mem_coeffCocycles⟩ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm.solution
