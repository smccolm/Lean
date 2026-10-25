import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Complex.Basic

/-! DUB-17/18 -> auxiliary compactness -> openness of restriction.
An actual chart comparison with a nonzero derivative transports the full
neighborhood filter. This supplies both continuity and openness, with no
pre-existing topology or compactness premise on the restriction map.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Filter Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem map_nhds_eq_of_analytic_chart_comparison (f : X → Y) {x : X}
    (e : OpenPartialHomeomorph X ℂ) (d : OpenPartialHomeomorph Y ℂ)
    (hx : x ∈ e.source) (hy : f x ∈ d.source)
    (g : ℂ → ℂ) (g' : ℂ) (hg : HasStrictDerivAt g g' (e x)) (hg' : g' ≠ 0)
    (hvalue : g (e x) = d (f x))
    (hcomp : ∀ᶠ z in 𝓝 (e x), f (e.symm z) = d.symm (g z)) :
    Filter.map f (𝓝 x) = 𝓝 (f x) := by
  have he : Filter.map e.symm (𝓝 (e x)) = 𝓝 x := by
    rw [e.symm.map_nhds_eq (e.map_source hx), e.left_inv hx]
  have hd : Filter.map d.symm (𝓝 (d (f x))) = 𝓝 (f x) := by
    rw [d.symm.map_nhds_eq (d.map_source hy), d.left_inv hy]
  calc
    Filter.map f (𝓝 x) = Filter.map f (Filter.map e.symm (𝓝 (e x))) := by rw [he]
    _ = Filter.map (fun z => f (e.symm z)) (𝓝 (e x)) := Filter.map_map
    _ = Filter.map (fun z => d.symm (g z)) (𝓝 (e x)) := Filter.map_congr hcomp
    _ = Filter.map d.symm (Filter.map g (𝓝 (e x))) := Filter.map_map.symm
    _ = 𝓝 (f x) := by rw [hg.map_nhds_eq hg', hvalue, hd]

end
end Dubon2026.SourceCurve
