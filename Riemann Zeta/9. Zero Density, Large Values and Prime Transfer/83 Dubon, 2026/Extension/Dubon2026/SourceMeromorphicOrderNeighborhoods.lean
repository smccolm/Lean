import Dubon2026.SourceMeromorphicRemovableCharts

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Analytic transition maps propagate zero germs
and isolated nonzero orders. Connectedness separates the identically zero
case; compactness makes the pole set finite. These results supply an actual
effective divisor for the proved original Riemann-Roch inequality.
Adapted from S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

theorem exists_ball_of_eventually_pf (v : M) {P : ℂ → Prop} (h : ∀ᶠ z in (𝓝[≠] (ctr v)), P z) :
    ∃ r > 0, Metric.ball (ctr v) r ⊆ (φ v).target ∧
      ∀ z ∈ Metric.ball (ctr v) r, z ≠ ctr v → P z := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (extChartAt_target_mem_nhds v))
  exact ⟨r, hr, fun z hz => (hball z hz).2, fun z hz hne => (hball z hz).1 hne⟩

theorem eventually_mem_source_and_ball (v : M) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ w in 𝓝 v, w ∈ (φ v).source ∧ φ v w ∈ Metric.ball (ctr v) r ∧ (w ≠ v → φ v w ≠ ctr v) := by
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) v,
    (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) v).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)]
    with w hw hb
  exact ⟨hw, hb, fun hne heq => hne ((φ v).injOn hw (mem_extChartAt_source v) heq)⟩

theorem rd_change (ψ : M → ℂ) {v w : M} (hw : w ∈ (φ v).source) :
    rd ψ w =ᶠ[𝓝 (ctr w)] (rd ψ v ∘ (φ v ∘ (φ w).symm)) := by
  have hs : ∀ᶠ z in 𝓝 (ctr w), (φ w).symm z ∈ (φ v).source :=
    eventually_symm_mem_source (mem_extChartAt_target w) (by rw [extChartAt_to_inv]; exact hw)
  filter_upwards [hs] with z hz
  exact rd_eq_comp ψ hz

variable [IsManifold 𝓘(ℂ, ℂ) ω M]

theorem eventually_order_eq_top (ψ : M → ℂ) {v : M} (hv : rd ψ v =ᶠ[(𝓝[≠] (ctr v))] 0) :
    ∀ᶠ w in 𝓝 v, meromorphicOrderAt (rd ψ w) (ctr w) = ⊤ := by

  have h1 : ∀ᶠ z in (𝓝[≠] (ctr v)), ∀ᶠ z' in 𝓝 z, rd ψ v z' = 0 := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at hv
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hv.eventually_nhds] with z hz hne
    have hne' : ∀ᶠ z' in 𝓝 z, z' ≠ ctr v := isOpen_compl_singleton.mem_nhds hne
    filter_upwards [hz, hne'] with z' h1 h2
    exact h1 h2
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually_pf v h1
  filter_upwards [eventually_mem_source_and_ball v hr] with w ⟨hws, hwb, hwne⟩
  by_cases hwv : w = v
  · rw [hwv]; exact meromorphicOrderAt_eq_top_iff.2 hv
  · have hz := hball _ hwb (hwne hwv)

    have hchg := rd_change ψ hws
    have hτc : ContinuousAt (φ v ∘ (φ w).symm) (ctr w) :=
      (analyticAt_transition v w (mem_extChartAt_target w)
        (by rw [extChartAt_to_inv]; exact hws)).continuousAt
    have hτ0 : (φ v ∘ (φ w).symm) (ctr w) = φ v w := by
      show φ v ((φ w).symm (ctr w)) = φ v w
      rw [extChartAt_to_inv]
    have hz' : ∀ᶠ z' in 𝓝 ((φ v ∘ (φ w).symm) (ctr w)), rd ψ v z' = 0 := by rw [hτ0]; exact hz
    apply meromorphicOrderAt_eq_top_iff.2
    apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [hchg, hτc.eventually hz'] with z h1 h2
    rw [h1]
    exact h2

theorem eventually_order_eq_zero (ψ : M → ℂ) {v : M}
    (hv' : MeromorphicAt (rd ψ v) (ctr v)) (hv : ∀ᶠ z in (𝓝[≠] (ctr v)), rd ψ v z ≠ 0) :
    ∀ᶠ w in 𝓝 v, w ≠ v →
      MeromorphicAt (rd ψ w) (ctr w) ∧ meromorphicOrderAt (rd ψ w) (ctr w) = 0 := by
  obtain ⟨r, hr, hB, hball⟩ := exists_ball_of_eventually_pf v (hv.and hv'.eventually_analyticAt)
  filter_upwards [eventually_mem_source_and_ball v hr] with w ⟨hws, hwb, hwne⟩ hwv
  obtain ⟨hne0, han⟩ := hball _ hwb (hwne hwv)
  have hchg := rd_change ψ hws
  have hτ : AnalyticAt ℂ (φ v ∘ (φ w).symm) (ctr w) :=
    analyticAt_transition v w (mem_extChartAt_target w) (by rw [extChartAt_to_inv]; exact hws)
  have hτ0 : (φ v ∘ (φ w).symm) (ctr w) = φ v w := by
    show φ v ((φ w).symm (ctr w)) = φ v w
    rw [extChartAt_to_inv]
  have hcomp : AnalyticAt ℂ (rd ψ v ∘ (φ v ∘ (φ w).symm)) (ctr w) := by
    refine AnalyticAt.comp ?_ hτ
    rw [hτ0]; exact han
  have han' : AnalyticAt ℂ (rd ψ w) (ctr w) := hcomp.congr hchg.symm
  refine ⟨han'.meromorphicAt, ?_⟩
  rw [han'.meromorphicOrderAt_eq, (han'.analyticOrderAt_eq_zero).2 ?_]
  · simp
  · rw [hchg.self_of_nhds, Function.comp_apply, hτ0]
    exact hne0



end
end Dubon2026.SourceFunctionField.MeromorphicCompact
