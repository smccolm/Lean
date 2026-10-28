import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty
    (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty.solution
