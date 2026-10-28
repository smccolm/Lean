import Mathlib
import P2M.Util
import P2M.Sol.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card

open scoped Manifold ContDiff Topology

theorem Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (D : M →₀ ℕ) {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ)
    (hψ : ∀ i x, MeromorphicAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hord : ∀ i x, ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x))
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x : M, (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] 0 := by p2m_exact_reverting @_root_.P2MW.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card.solution
