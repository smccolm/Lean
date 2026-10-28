import Mathlib
import P2M.Util
import P2M.Sol.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg

open scoped Manifold ContDiff Topology

theorem Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (g : M → ℂ)
    (hg : ∀ x : M, MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hg0 : ∀ x : M, 0 ≤ meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x)) :
    ∃ C : ℂ, ∀ x : M, (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] fun _ => C := by p2m_exact_reverting @_root_.P2MW.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg.solution
