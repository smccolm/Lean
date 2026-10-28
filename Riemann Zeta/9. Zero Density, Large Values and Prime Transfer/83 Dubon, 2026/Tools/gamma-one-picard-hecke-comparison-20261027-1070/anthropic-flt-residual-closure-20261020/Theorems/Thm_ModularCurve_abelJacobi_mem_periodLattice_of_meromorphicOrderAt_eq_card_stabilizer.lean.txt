import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
    {N : ℕ} [NeZero N] (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2 : ℕ) *
        Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)) c
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) τ) : ℤ) :
        WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer.solution
