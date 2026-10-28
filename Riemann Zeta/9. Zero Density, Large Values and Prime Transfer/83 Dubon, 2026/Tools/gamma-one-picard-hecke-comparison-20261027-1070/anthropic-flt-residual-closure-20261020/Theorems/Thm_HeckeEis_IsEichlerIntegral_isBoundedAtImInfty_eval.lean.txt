import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hbdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hT : ∀ τ : UpperHalfPlane, G ((h : ℝ) +ᵥ τ) = HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.solution
