import Dubon2026.SourceOriginalComplexChartOrders
import Dubon2026.SourceOriginalPlaceSeparation

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
The constructed original complex manifold is Hausdorff. A function with
positive order at one place and negative order at the other separates
small chart disks by the norms of its value and reciprocal. Actual
rank-one valuation rings and residues supply this function directly.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_small_place_disc (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {f : modularFunctionFieldOver N ℂ} (hf : f ≠ 0) (hv : 0 < v.ord f) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ placeRadius N v ∧ ∀ z ∈ ball 0 δ,
      f ∈ (placeFamily N v z).toValuationSubring ∧
        ‖originalPlaceEval N ℂ (placeFamily N v z) f‖ < 1 := by
  let F : ℂ → ℂ := fun z => originalPlaceEval N ℂ (placeFamily N v z) f
  have hmem : f ∈ (placeFamily N v 0).toValuationSubring := by
    rw [(place_spec N v).2.1]
    exact v.mem_of_ord_nonneg hv.le
  have ha : AnalyticAt ℂ F 0 := (place_spec N v).2.2.1.analyticAt
    (mem_ball_self (place_spec N v).1) hmem
  have h0 : F 0 = 0 := by
    dsimp only [F]
    rw [(place_spec N v).2.1]
    exact (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v (v.mem_of_ord_nonneg hv.le) hf).mpr hv
  have hm := (place_spec N v).2.2.1.eventually_mem
    (ball_mem_nhds 0 (place_spec N v).1) hmem
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < 1 := by
    have hc := ha.continuousAt.norm
    rw [ContinuousAt, h0, norm_zero] at hc
    exact hc.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hm.and hn)
  refine ⟨min δ (placeRadius N v), lt_min hδ (place_spec N v).1, min_le_right _ _, fun z hz => ?_⟩
  exact hball z (ball_subset_ball (min_le_left _ _) hz)

theorem place_t2Space : @T2Space (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) := by
  letI := placeTopology N
  refine ⟨fun v w hne => ?_⟩
  obtain ⟨f, hf, hv, hw⟩ := original_places_separating_function N v w hne
  have hwi : 0 < w.ord f⁻¹ := by rw [w.ord_inv]; exact neg_pos.mpr hw
  obtain ⟨δ, hδ, hδR, hvδ⟩ := exists_small_place_disc N v hf hv
  obtain ⟨ε, hε, hεR, hwε⟩ := exists_small_place_disc N w (inv_ne_zero hf) hwi
  refine ⟨placeFamily N v '' ball 0 δ, placeFamily N w '' ball 0 ε,
    isOpen_placeFamily_image N v isOpen_ball (ball_subset_ball hδR),
    isOpen_placeFamily_image N w isOpen_ball (ball_subset_ball hεR),
    ⟨0, mem_ball_self hδ, (place_spec N v).2.1⟩,
    ⟨0, mem_ball_self hε, (place_spec N w).2.1⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro P ⟨z, hz, rfl⟩ ⟨u, hu, he⟩
  obtain ⟨hmem, hlt⟩ := hvδ z hz
  obtain ⟨hmem', hlt'⟩ := hwε u hu
  rw [he] at hmem' hlt'
  have hval : originalPlaceEval N ℂ (placeFamily N v z) f ≠ 0 := by
    intro h0
    have hpos := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ (placeFamily N v z) hmem hf).mp h0
    have hnonneg := (placeFamily N v z).ord_nonneg_of_mem hmem'
    rw [(placeFamily N v z).ord_inv] at hnonneg
    omega
  have hprod : originalPlaceEval N ℂ (placeFamily N v z) f *
      originalPlaceEval N ℂ (placeFamily N v z) f⁻¹ = 1 := by
    rw [originalPlaceEval_inv, mul_inv_cancel₀ hval]
  have hnorm : ‖originalPlaceEval N ℂ (placeFamily N v z) f *
      originalPlaceEval N ℂ (placeFamily N v z) f⁻¹‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ 1 * ‖originalPlaceEval N ℂ (placeFamily N v z) f⁻¹‖ :=
           mul_le_mul_of_nonneg_right hlt.le (norm_nonneg _)
         _ < 1 := by simpa only [one_mul] using hlt'
  rw [hprod, norm_one] at hnorm
  exact lt_irrefl _ hnorm

end
end Dubon2026.SourceFunctionField.OriginalChart
