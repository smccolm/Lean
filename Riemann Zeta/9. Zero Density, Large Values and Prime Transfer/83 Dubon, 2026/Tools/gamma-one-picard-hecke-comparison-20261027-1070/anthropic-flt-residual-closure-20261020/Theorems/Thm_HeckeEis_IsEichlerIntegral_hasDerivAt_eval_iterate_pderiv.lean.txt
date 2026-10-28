import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n)
    (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => MvPolynomial.eval ![(1 : ℂ), -z]
        ((MvPolynomial.pderiv 1)^[j]
          ((G (UpperHalfPlane.ofComplex z) : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)
        - MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)]
          ((MvPolynomial.pderiv 1)^[j + 1] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      (τ : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.solution
