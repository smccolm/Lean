import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Analysis.Complex.Basic

/-! DUB-17/18 -> cover raw reciprocity -> lifted original cells.
A nonzero-derivative comparison of the actual charts makes the restriction
locally injective. The already proved continuity and openness then give a
local homeomorphism. Only this exact covering criterion is developed here. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Filter Topology Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_nhds_injOn_of_analytic_chart_comparison (f : X → Y) {x : X}
    (e : OpenPartialHomeomorph X ℂ) (d : OpenPartialHomeomorph Y ℂ)
    (hx : x ∈ e.source) (hy : f x ∈ d.source)
    (g : ℂ → ℂ) (g' : ℂ) (hg : HasStrictDerivAt g g' (e x)) (hg' : g' ≠ 0)
    (hvalue : g (e x) = d (f x))
    (hcomp : ∀ᶠ z in 𝓝 (e x), f (e.symm z) = d.symm (g z)) :
    ∃ U ∈ 𝓝 x, U.InjOn f := by
  let inv := hg.localInverse g g' (e x) hg'
  have hleft : ∀ᶠ z in 𝓝 (e x), inv (g z) = z := hg.eventually_left_inverse hg'
  have ht : g (e x) ∈ d.target := by rw [hvalue]; exact d.map_source hy
  have htarget : ∀ᶠ z in 𝓝 (e x), g z ∈ d.target :=
    hg.hasDerivAt.continuousAt.eventually (d.open_target.mem_nhds ht)
  have hc := e.continuousAt hx
  have hnear : ∀ᶠ y in 𝓝 x,
      y ∈ e.source ∧ f y = d.symm (g (e y)) ∧ g (e y) ∈ d.target ∧ inv (g (e y)) = e y := by
    filter_upwards [e.open_source.mem_nhds hx, hc.eventually hcomp,
      hc.eventually htarget, hc.eventually hleft] with y hys hcompy hty hly
    exact ⟨hys, by simpa only [e.left_inv hys] using hcompy, hty, hly⟩
  refine ⟨{y | y ∈ e.source ∧ f y = d.symm (g (e y)) ∧ g (e y) ∈ d.target ∧ inv (g (e y)) = e y},
    hnear, ?_⟩
  intro y hy z hz heq
  have he : g (e y) = g (e z) := d.symm.injOn hy.2.2.1 hz.2.2.1
    (by rw [← hy.2.1, ← hz.2.1]; exact heq)
  exact e.injOn hy.1 hz.1 (hy.2.2.2.symm.trans ((congrArg inv he).trans hz.2.2.2))

theorem isLocalHomeomorph_of_continuous_open_locally_injective (f : X → Y)
    (hf : Continuous f) (ho : IsOpenMap f)
    (hi : ∀ x, ∃ U ∈ 𝓝 x, U.InjOn f) : IsLocalHomeomorph f := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U, hU, hI⟩ := hi x
  refine ⟨interior U, isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU), ?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨hf.comp continuous_subtype_val, Set.injOn_iff_injective.mp (hI.mono interior_subset),
    ho.comp isOpen_interior.isOpenMap_subtype_val⟩

end
end Dubon2026.SourceCurve
