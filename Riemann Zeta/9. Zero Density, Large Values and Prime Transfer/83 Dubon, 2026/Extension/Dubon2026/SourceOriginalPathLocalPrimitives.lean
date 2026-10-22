import Dubon2026.SourceOriginalDifferentialTransitions
import Dubon2026.SourceOriginalChartPrimitives
import Dubon2026.SourceComplexPrimitiveGluing

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> path periods.
The proved differential transition law transports one actual chart
primitive to all nearby points of a continuous path. This supplies the
local-existence input of interval gluing from original regularity alone.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem continuousAt_placeChart (v w : Place ℂ (modularFunctionFieldOver N ℂ))
    (hw : w ∈ (placeChart N v).source) :
    letI := placeTopology N
    ContinuousAt (placeChart N v) w := by
  letI := placeTopology N
  exact ((placeCore N).openPartialHomeomorph (placeChart N v) ⟨v, rfl⟩).continuousAt hw

theorem placeChart_source_mem_nhds (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    letI := placeTopology N
    (placeChart N v).source ∈ 𝓝 v := by
  letI := placeTopology N
  exact ((placeCore N).openPartialHomeomorph (placeChart N v) ⟨v, rfl⟩).open_source.mem_nhds
    (mem_placeChart_source N v)

theorem exists_original_path_local_primitive
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (c : ℝ → Place ℂ (modularFunctionFieldOver N ℂ))
    (hc : letI := placeTopology N; Continuous c) (s : ℝ) :
    ∃ G : ℝ → ℂ, ∀ᶠ t₀ in 𝓝 s,
      IsPrimNear (fun t z => readDifferential N (c t) ω z)
        (fun t₀ t => placeChart N (c t₀) (c t)) G t₀ := by
  letI := placeTopology N
  obtain ⟨Φ, hΦ⟩ := exists_readDifferential_primitive_on_chart N (c s) ω hω
  refine ⟨fun t => Φ (placeChart N (c s) (c t)), ?_⟩
  have hs : ∀ᶠ t₀ in 𝓝 s, c t₀ ∈ (placeChart N (c s)).source :=
    hc.continuousAt.eventually (placeChart_source_mem_nhds N (c s))
  filter_upwards [hs] with t₀ ht₀
  let T := chartRead N (c t₀) (c s).uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N (c t₀)
    (uniformizer_regular_on_chart N (c s) (c t₀) ht₀)
  have hT0 : T 0 ∈ ball 0 (placeRadius N (c s)) := by
    change originalPlaceEval N ℂ (placeFamily N (c t₀) 0) (c s).uniformizer ∈ _
    rw [(place_spec N (c t₀)).2.1]
    exact (placeChart N (c s)).map_source ht₀
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ ball 0 (placeRadius N (c s)) :=
    hT.continuousAt.eventually (isOpen_ball.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · dsimp only
    rw [placeChart_self]
    filter_upwards [readDifferential_change N (c s) (c t₀) ω hω ht₀,
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, c t ∈ (placeChart N (c t₀)).source :=
      hc.continuousAt.eventually (placeChart_source_mem_nhds N (c t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N (c s) (c t)) =
      Φ (placeChart N (c s) (placeFamily N (c t₀) (placeChart N (c t₀) (c t))))
    rw [show placeFamily N (c t₀) (placeChart N (c t₀) (c t)) = c t from
      (placeChart N (c t₀)).left_inv ht]

end
end Dubon2026.SourceFunctionField.OriginalChart
