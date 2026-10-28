import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero
    {N : ℕ} [NeZero N] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (t : ℂ)
    (hne : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    Set.Finite (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) ''
      {τ : ℍ | meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ 0}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finite_image_orbitRel_meromorphicOrderAt_sub_ne_zero.solution
