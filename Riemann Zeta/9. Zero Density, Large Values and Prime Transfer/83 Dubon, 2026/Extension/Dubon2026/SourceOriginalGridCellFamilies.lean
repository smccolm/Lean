import Dubon2026.SourceOriginalGridRegionSheets
import Dubon2026.SourceOriginalBranchedCells
import Dubon2026.SourceOriginalPoleCells

/-! DUB-17/18 -> original Abel-Jacobi -> finite geometric cell assembly.
These records retain the actual analytic cells and every evaluation, power,
reciprocal-arc and coverage conclusion needed by the global pairing. They
are data interfaces; their existence is proved from the original j map.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- Actual analytic sheets with one fixed radial region and exact carrier coverage. -/
structure OriginalOrdinaryRegionFamily (R : RadialRegion) where
  /-- Open common target of the analytic sheets. -/
  V : Set ℂ
  /-- Actual ordinary cells, one for each sheet. -/
  C : Fin (SourceLevelProjective.dedekindPsi N) → Cell N
  isOpen : IsOpen V
  region_subset : R.K ⊆ V
  zero_notMem : (0 : ℂ) ∉ V
  branch_notMem : (1728 : ℂ) ∉ V
  region_eq : ∀ i, (C i).R = R
  sheets : IsOriginalSheetFamily (jOver N ℂ) V (fun i => (C i).ζ)
  coverage : ∀ P : Place ℂ F,
    (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.K) ↔
    ∃ i, P ∈ (C i).carrier
  disjoint : Pairwise (fun i i' => Disjoint (C i).carrier (C i').carrier)

/-- Exact powered cells at a prescribed original j fiber. -/
structure OriginalBranchRegionFamily (b : ℂ) (R : RadialRegion) where
  /-- Actual powered cells, one for each original point over the branch value. -/
  C : originalPositiveFiber N (jOver N ℂ) b → Cell N
  geometry : ∀ v : originalPositiveFiber N (jOver N ℂ) b,
    (v : Place ℂ F) ∈ (C v).interior' ∧ (C v).ζ v = 0 ∧
    PowPullback.PowerGeometry R
      ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat (C v).R ∧
    ∀ P ∈ (C v).ζ.source, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) = b + (C v).ζ P ^
        ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat
  disjoint : Pairwise (fun v w => Disjoint (C v).carrier (C w).carrier)
  coverage : ∀ P : Place ℂ F,
    (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.K) ↔
    ∃ v, P ∈ (C v).carrier

/-- Reciprocal and powered cells covering precisely the original j exterior. -/
structure OriginalPoleRegionFamily (W : RadialRegion) where
  /-- Reciprocal region corresponding to the outer window. -/
  R : RadialRegion
  /-- Actual powered cells at the original poles of j. -/
  C : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 → Cell N
  reciprocal : RadialRecip.ReciprocalGeometry W R
  geometry : ∀ v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0,
    (v : Place ℂ F) ∈ (C v).interior' ∧ (C v).ζ v = 0 ∧
    PowPullback.PowerGeometry R ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat (C v).R ∧
    ∀ P ∈ (C v).ζ.source, (jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = (C v).ζ P ^
        ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat
  disjoint : Pairwise (fun v w => Disjoint (C v).carrier (C w).carrier)
  coverage : ∀ P : Place ℂ F,
    (jOver N ℂ ∉ P.toValuationSubring ∨
      (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∉ W.Kint)) ↔
    ∃ v, P ∈ (C v).carrier

theorem exists_original_ordinary_region_family {o h : ℝ} (hh : 0 < h) (j k : ℤ)
    (R : RadialRegion) (hRK : R.K = SquareGrid.gridSquare o h j k)
    (h0 : (0 : ℂ) ∉ SquareGrid.gridSquare o h j k)
    (h1728 : (1728 : ℂ) ∉ SquareGrid.gridSquare o h j k) :
    Nonempty (OriginalOrdinaryRegionFamily N R) := by
  obtain ⟨V, C, hV, hR, h0, h1728, hreg, hsheet, hcover, hd⟩ :=
    exists_original_square_cells_for_region N hh j k R hRK h0 h1728
  exact ⟨⟨V, C, hV, hR, h0, h1728, hreg, hsheet, hcover, hd⟩⟩

theorem exists_original_branch_region_family (b : ℂ) :
    ∃ ε > 0, ∀ R : RadialRegion, R.q = b → 2 ≤ R.N → R.K ⊆ Metric.ball b ε →
      Nonempty (OriginalBranchRegionFamily N b R) := by
  obtain ⟨ε, hε, hC⟩ := exists_original_j_branch_cells N b
  refine ⟨ε, hε, ?_⟩
  intro R hq hN hK
  obtain ⟨C, hg, hd, hc⟩ := hC R hq hN hK
  exact ⟨⟨C, hg, hd, hc⟩⟩

theorem exists_original_pole_region_family :
    ∃ B > 0, ∀ W : RadialRegion, W.q = 0 → 2 ≤ W.N → Metric.closedBall 0 B ⊆ W.Kint →
      Nonempty (OriginalPoleRegionFamily N W) := by
  obtain ⟨B, hB, hC⟩ := exists_original_j_pole_cells N
  refine ⟨B, hB, ?_⟩
  intro W hq hN hK
  obtain ⟨R, C, hR, hg, hd, hc⟩ := hC W hq hN hK
  exact ⟨⟨R, C, hR, hg, hd, hc⟩⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
