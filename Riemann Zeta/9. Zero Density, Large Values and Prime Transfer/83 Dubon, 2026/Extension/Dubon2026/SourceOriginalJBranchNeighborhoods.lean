import Dubon2026.SourceOriginalNormalFiberNeighborhoods
import Dubon2026.SourceOriginalJFiberDegree

/-! DUB-17/18 -> geometric cell dissection -> finite branch-value caps.
Specialize the constructed disjoint normal neighborhoods to the actual j
fiber, preserving its original exponent, chart regularity and full nearby
fiber exhaustion. No branch-chart input is supplied by the caller.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
open scoped Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_j_branch_neighborhoods (b : ℂ) :
    ∃ (A : originalPositiveFiber N (jOver N ℂ) b → AnalyticCoord N)
      (r : originalPositiveFiber N (jOver N ℂ) b → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ v : originalPositiveFiber N (jOver N ℂ) b,
        0 < r v ∧ (v : Place ℂ F) ∈ (A v).ζ.source ∧ (A v).ζ v = 0 ∧
        (A v).ζ.target = Metric.ball 0 (r v) ∧
        (A v).ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) (v : Place ℂ F)).source ∧
        0 < ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat ∧
        ∀ P ∈ (A v).ζ.source, jOver N ℂ ∈ P.toValuationSubring ∧
          originalPlaceEval N ℂ P (jOver N ℂ) =
            b + ((A v).ζ P) ^ ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat) ∧
      (Pairwise fun v w => Disjoint (A v).ζ.source (A w).ζ.source) ∧
      (∀ v : originalPositiveFiber N (jOver N ℂ) b,
        ε < r v ^ ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat) ∧
      ∀ P : Place ℂ F, jOver N ℂ ∈ P.toValuationSubring →
        ‖originalPlaceEval N ℂ P (jOver N ℂ) - b‖ < ε →
        ∃ v : originalPositiveFiber N (jOver N ℂ) b, P ∈ (A v).ζ.source := by
  have hg : ∀ c : ℂ, jOver N ℂ - algebraMap ℂ F b ≠ algebraMap ℂ F c :=
    fun c h => original_j_sub_transcendental N ℂ b (h ▸ isAlgebraic_algebraMap c)
  have hnormal := exists_original_normal_fiber_neighborhoods hg
  have hS : originalPositiveFiber N (jOver N ℂ - algebraMap ℂ F b) 0 =
      originalPositiveFiber N (jOver N ℂ) b := by
    ext v
    simp only [mem_originalPositiveFiber, map_zero, sub_zero]
  rw [hS] at hnormal
  obtain ⟨A, r, ε, hε, hA, hd, hr, hcover⟩ := hnormal
  refine ⟨A, r, ε, hε, ?_, hd, hr, ?_⟩
  · intro v
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hA v
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    intro P hP
    obtain ⟨hPg, hval⟩ := h7 P hP
    have hPj := (original_sub_const_mem_iff N P (jOver N ℂ) b).mp hPg
    refine ⟨hPj, ?_⟩
    rw [originalPlaceEval_sub_algebraMap N ℂ P hPj] at hval
    exact sub_eq_iff_eq_add'.mp hval
  · intro P hPj hsmall
    apply hcover P (sub_mem hPj (P.algebraMap_mem' b))
    rwa [originalPlaceEval_sub_algebraMap N ℂ P hPj]

end
end Dubon2026.SourceFunctionField.CellGeometry
