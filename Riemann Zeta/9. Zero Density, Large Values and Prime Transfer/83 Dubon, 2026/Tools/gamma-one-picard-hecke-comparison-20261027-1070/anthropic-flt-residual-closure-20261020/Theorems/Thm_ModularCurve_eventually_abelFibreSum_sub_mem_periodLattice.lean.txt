import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSum
import P2M.Util
import P2M.Sol.S_ModularCurve_eventually_abelFibreSum_sub_mem_periodLattice
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.eventually_abelFibreSum_sub_mem_periodLattice
    {N : ℕ} [NeZero N] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hnc : ∀ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ᶠ t in 𝓝 t₀,
      ModularCurve.abelFibreSum N F t - ModularCurve.abelFibreSum N F t₀ ∈
        ModularCurve.periodLattice N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eventually_abelFibreSum_sub_mem_periodLattice.solution
