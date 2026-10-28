import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane)
    (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    HeckeEis.jFactor g τ ^ n * MvPolynomial.eval ![(1 : ℂ), -(((g • τ : UpperHalfPlane)) : ℂ)]
        ((HeckeEis.binaryFormRepSL ℂ n g P : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] (P : MvPolynomial (Fin 2) ℂ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.solution
