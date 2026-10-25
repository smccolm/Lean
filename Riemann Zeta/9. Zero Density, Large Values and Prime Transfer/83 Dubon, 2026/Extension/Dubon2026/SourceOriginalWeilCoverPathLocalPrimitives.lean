import Dubon2026.SourceOriginalWeilCoverDifferentialTransitions
import Dubon2026.SourceOriginalWeilCoverChartPrimitives
import Dubon2026.SourceComplexPrimitiveGluing

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel comparison.
Adapt the proved original-curve coordinate and primitive arguments to the
literal Kummer cover, using its constructed charts and finite coordinate.
The primitive gluing argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem continuousAt_placeChart (v w : Place ℂ (EE))
    (hw : w ∈ (placeChart N n r A hr hrA v).source) :
    letI := placeTopology N n r A hr hrA
    ContinuousAt (placeChart N n r A hr hrA v) w := by
  letI := placeTopology N n r A hr hrA
  exact ((placeCore N n r A hr hrA).openPartialHomeomorph (placeChart N n r A hr hrA v) ⟨v, rfl⟩).continuousAt hw

theorem placeChart_source_mem_nhds (v : Place ℂ (EE)) :
    letI := placeTopology N n r A hr hrA
    (placeChart N n r A hr hrA v).source ∈ 𝓝 v := by
  letI := placeTopology N n r A hr hrA
  exact ((placeCore N n r A hr hrA).openPartialHomeomorph (placeChart N n r A hr hrA v) ⟨v, rfl⟩).open_source.mem_nhds
    (mem_placeChart_source N n r A hr hrA v)

theorem exists_cover_path_local_primitive
    (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    (c : ℝ → Place ℂ (EE))
    (hc : letI := placeTopology N n r A hr hrA; Continuous c) (s : ℝ) :
    ∃ G : ℝ → ℂ, ∀ᶠ t₀ in 𝓝 s,
      IsPrimNear (fun t z => readDifferential N n r A hr hrA (c t) ω z)
        (fun t₀ t => placeChart N n r A hr hrA (c t₀) (c t)) G t₀ := by
  letI := placeTopology N n r A hr hrA
  obtain ⟨Φ, hΦ⟩ := exists_readDifferential_primitive_on_chart N n r A hr hrA (c s) ω hω
  refine ⟨fun t => Φ (placeChart N n r A hr hrA (c s) (c t)), ?_⟩
  have hs : ∀ᶠ t₀ in 𝓝 s, c t₀ ∈ (placeChart N n r A hr hrA (c s)).source :=
    hc.continuousAt.eventually (placeChart_source_mem_nhds N n r A hr hrA (c s))
  filter_upwards [hs] with t₀ ht₀
  let T := chartRead N n r A hr hrA (c t₀) (c s).uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N n r A hr hrA (c t₀)
    (uniformizer_regular_on_chart N n r A hr hrA (c s) (c t₀) ht₀)
  have hT0 : T 0 ∈ ball 0 (placeRadius N n r A hr hrA (c s)) := by
    change (placeFamily N n r A hr hrA (c t₀) 0).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r _) (c s).uniformizer ∈ _
    rw [(place_spec N n r A hr hrA (c t₀)).2.1]
    exact (placeChart N n r A hr hrA (c s)).map_source ht₀
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ ball 0 (placeRadius N n r A hr hrA (c s)) :=
    hT.continuousAt.eventually (isOpen_ball.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · dsimp only
    rw [placeChart_self]
    filter_upwards [readDifferential_change N n r A hr hrA (c s) (c t₀) ω hω ht₀,
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, c t ∈ (placeChart N n r A hr hrA (c t₀)).source :=
      hc.continuousAt.eventually (placeChart_source_mem_nhds N n r A hr hrA (c t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N n r A hr hrA (c s) (c t)) =
      Φ (placeChart N n r A hr hrA (c s) (placeFamily N n r A hr hrA (c t₀) (placeChart N n r A hr hrA (c t₀) (c t))))
    rw [show placeFamily N n r A hr hrA (c t₀) (placeChart N n r A hr hrA (c t₀) (c t)) = c t from
      (placeChart N n r A hr hrA (c t₀)).left_inv ht]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
