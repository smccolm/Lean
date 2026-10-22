import Dubon2026.SourceOriginalAbelJacobiPeriods
import Mathlib.Analysis.Convex.PathConnected

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> local period coordinates.
A primitive on an original chart represents integration along any path
inside that chart. Native path connectedness of the chart disk supplies
such paths to every point in the disk. This avoids an additional explicit
segment parameterization while preserving the actual path integral.
The argument adapts the chart-path part of
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem isPrimitiveAlong_of_chart_primitive
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ ball (0 : ℂ) (placeRadius N v), HasDerivAt Φ (readDifferential N v ω z) z)
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P Q)
    (hγ : ∀ t, γ t ∈ (placeChart N v).source) :
    IsPrimitiveAlong N ω γ (fun t => Φ (placeChart N v (γ t))) := by
  intro t₀
  let T := chartRead N (γ t₀) v.uniformizer
  have hT : AnalyticAt ℂ T 0 := analyticAt_place_reading N (γ t₀)
    (uniformizer_regular_on_chart N v (γ t₀) (hγ t₀))
  have hT0 : T 0 ∈ ball 0 (placeRadius N v) := by
    change originalPlaceEval N ℂ (placeFamily N (γ t₀) 0) v.uniformizer ∈ _
    rw [(place_spec N (γ t₀)).2.1]
    exact (placeChart N v).map_source (hγ t₀)
  have hb : ∀ᶠ z in 𝓝 (0 : ℂ), T z ∈ ball 0 (placeRadius N v) :=
    hT.continuousAt.eventually (isOpen_ball.mem_nhds hT0)
  refine ⟨Φ ∘ T, ?_, ?_⟩
  · rw [placeChart_self]
    filter_upwards [readDifferential_change N v (γ t₀) ω hω (hγ t₀),
      hT.eventually_analyticAt, hb] with z hchange hz hzb
    rw [hchange]
    exact (hΦ (T z) hzb).comp z hz.differentiableAt.hasDerivAt
  · have hm : ∀ᶠ t in 𝓝 t₀, γ t ∈ (placeChart N (γ t₀)).source :=
      γ.continuous.continuousAt.eventually (placeChart_source_mem_nhds N (γ t₀))
    filter_upwards [hm] with t ht
    change Φ (placeChart N v (γ t)) =
      Φ (placeChart N v (placeFamily N (γ t₀) (placeChart N (γ t₀) (γ t))))
    rw [show placeFamily N (γ t₀) (placeChart N (γ t₀) (γ t)) = γ t from
      (placeChart N (γ t₀)).left_inv ht]

theorem exists_original_chart_path (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    ∃ γ : Path v (placeFamily N v z), ∀ t, γ t ∈ (placeChart N v).source := by
  have h0 : (0 : ℂ) ∈ ball 0 (placeRadius N v) := mem_ball_self (place_spec N v).1
  obtain ⟨δ, hδ⟩ := ((convex_ball (0 : ℂ) (placeRadius N v)).isPathConnected ⟨0, h0⟩).joinedIn
    0 h0 z hz
  have hc : ContinuousOn (placeFamily N v) (range δ) :=
    (continuousOn_placeFamily N v).mono (by rintro _ ⟨t, rfl⟩; exact hδ t)
  refine ⟨(δ.map' hc).cast (place_spec N v).2.1.symm rfl, ?_⟩
  intro t
  exact ⟨δ t, hδ t, rfl⟩

theorem exists_original_chart_path_integrals {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (Φ : Fin n → ℂ → ℂ)
    (hΦ : ∀ i, ∀ z ∈ ball (0 : ℂ) (placeRadius N v),
      HasDerivAt (Φ i) (readDifferential N v (b i) z) z)
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    ∃ γ : Path v (placeFamily N v z), ∀ i, pathIntegral N (b i) γ = Φ i z - Φ i 0 := by
  obtain ⟨γ, hγ⟩ := exists_original_chart_path N v hz
  refine ⟨γ, fun i => ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N
    (isPrimitiveAlong_of_chart_primitive N (b i) (hb i) v (Φ i) (hΦ i) γ hγ)]
  rw [γ.target, γ.source, placeChart_self]
  have he : placeChart N v (placeFamily N v z) = z := place_eval_uniformizer N v hz
  rw [he]

end
end Dubon2026.SourceFunctionField.OriginalChart
