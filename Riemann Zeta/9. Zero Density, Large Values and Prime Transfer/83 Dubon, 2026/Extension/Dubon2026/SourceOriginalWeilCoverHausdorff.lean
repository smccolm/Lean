import Dubon2026.SourceOriginalWeilCoverChartOrders
import Dubon2026.SourceCurveRationalPlaceSeparation

/-! DUB-17/18 -> auxiliary cover Abel comparison -> Hausdorff complex cover.
The native valuation-ring separating function and continuous actual residue
readings separate small cover-chart disks. The topology is the one constructed
from the actual cover uniformizer charts. Compactness and connectedness remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Polynomial Filter Set Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])
variable (D : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hf : f ≠ 0)
variable (hfD : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord f = (n : ℤ) * D v)
include D hf hfD

theorem exists_small_place_disc (v : Place ℂ EE)
    {a : EE} (ha0 : a ≠ 0) (hv : 0 < v.ord a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ placeRadius N n f D hf hfD v ∧ ∀ z ∈ ball 0 δ,
      a ∈ (placeFamily N n f D hf hfD v z).toValuationSubring ∧
        ‖(placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a‖ < 1 := by
  let F : ℂ → ℂ := fun z => (placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a
  have hmem : a ∈ (placeFamily N n f D hf hfD v 0).toValuationSubring := by
    simp only [(place_spec N n f D hf hfD v).2.1]
    exact v.mem_of_ord_nonneg hv.le
  have ha : AnalyticAt ℂ F 0 := (place_spec N n f D hf hfD v).2.2.1.analyticAt
    (mem_ball_self (place_spec N n f D hf hfD v).1) hmem
  have h0 : F 0 = 0 := by
    dsimp only [F]
    simp only [(place_spec N n f D hf hfD v).2.1]
    exact (v.rationalEval_eq_zero_iff_ord_pos (originalWeilKummerCover_residue_bijective N ℂ n f v) (v.mem_of_ord_nonneg hv.le) ha0).mpr hv
  have hm := (place_spec N n f D hf hfD v).2.2.1.eventually_mem
    (ball_mem_nhds 0 (place_spec N n f D hf hfD v).1) hmem
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < 1 := by
    have hc := ha.continuousAt.norm
    rw [ContinuousAt, h0, norm_zero] at hc
    exact hc.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hm.and hn)
  refine ⟨min δ (placeRadius N n f D hf hfD v), lt_min hδ (place_spec N n f D hf hfD v).1, min_le_right _ _, fun z hz => ?_⟩
  exact hball z (ball_subset_ball (min_le_left _ _) hz)

theorem place_t2Space : @T2Space (Place ℂ EE) (placeTopology N n f D hf hfD) := by
  letI := placeTopology N n f D hf hfD
  refine ⟨fun v w hne => ?_⟩
  obtain ⟨a, ha, hv, hw⟩ := Place.exists_order_separating_function v w
    (originalWeilKummerCover_residue_bijective N ℂ n f v) hne
  have hwi : 0 < w.ord a⁻¹ := by rw [w.ord_inv]; exact neg_pos.mpr hw
  obtain ⟨δ, hδ, hδR, hvδ⟩ := exists_small_place_disc N n f D hf hfD v ha hv
  obtain ⟨ε, hε, hεR, hwε⟩ := exists_small_place_disc N n f D hf hfD w (inv_ne_zero ha) hwi
  refine ⟨placeFamily N n f D hf hfD v '' ball 0 δ, placeFamily N n f D hf hfD w '' ball 0 ε,
    isOpen_placeFamily_image N n f D hf hfD v isOpen_ball (ball_subset_ball hδR),
    isOpen_placeFamily_image N n f D hf hfD w isOpen_ball (ball_subset_ball hεR),
    ⟨0, mem_ball_self hδ, (place_spec N n f D hf hfD v).2.1⟩,
    ⟨0, mem_ball_self hε, (place_spec N n f D hf hfD w).2.1⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro P ⟨z, hz, rfl⟩ ⟨u, hu, he⟩
  obtain ⟨hmem, hlt⟩ := hvδ z hz
  obtain ⟨hmem', hlt'⟩ := hwε u hu
  simp only [he] at hmem' hlt'
  have hval : (placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a ≠ 0 := by
    intro h0
    have hpos := ((placeFamily N n f D hf hfD v z).rationalEval_eq_zero_iff_ord_pos (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) hmem ha).mp h0
    have hnonneg := (placeFamily N n f D hf hfD v z).ord_nonneg_of_mem hmem'
    rw [(placeFamily N n f D hf hfD v z).ord_inv] at hnonneg
    omega
  have hprod : (placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a *
      (placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a⁻¹ = 1 := by
    rw [Place.rationalEval_inv, mul_inv_cancel₀ hval]
  have hnorm : ‖(placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a *
      (placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a⁻¹‖ < 1 := by
    rw [norm_mul]
    calc _ ≤ 1 * ‖(placeFamily N n f D hf hfD v z).rationalEval (originalWeilKummerCover_residue_bijective N ℂ n f (placeFamily N n f D hf hfD v z)) a⁻¹‖ :=
           mul_le_mul_of_nonneg_right hlt.le (norm_nonneg _)
         _ < 1 := by simpa only [one_mul] using hlt'
  rw [hprod, norm_one] at hnorm
  exact lt_irrefl _ hnorm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
