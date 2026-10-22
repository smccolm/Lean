import Dubon2026.SourceOriginalFiniteNormalCoordinates
import Dubon2026.SourceOriginalPrescribedFiberCover

/-! DUB-17/18 -> geometric cell dissection -> complete branch neighborhoods.
The finite disjoint normal charts cover every sufficiently small nearby
fiber. Reuse the already proved compact-curve prescribed-fiber theorem,
avoiding the external repeated root-count and degree-exhaustion argument.
The common scale also lies strictly inside every normal chart image.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
open scoped Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_normal_fiber_neighborhoods {g : F}
    (hg : ∀ c : ℂ, g ≠ algebraMap ℂ F c) :
    ∃ (A : originalPositiveFiber N g 0 → AnalyticCoord N)
      (r : originalPositiveFiber N g 0 → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ v : originalPositiveFiber N g 0,
        0 < r v ∧ (v : Place ℂ F) ∈ (A v).ζ.source ∧ (A v).ζ v = 0 ∧
        (A v).ζ.target = Metric.ball 0 (r v) ∧
        (A v).ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) (v : Place ℂ F)).source ∧
        0 < ((v : Place ℂ F).ord g).toNat ∧
        ∀ P ∈ (A v).ζ.source, g ∈ P.toValuationSubring ∧
          originalPlaceEval N ℂ P g = ((A v).ζ P) ^ ((v : Place ℂ F).ord g).toNat) ∧
      (Pairwise fun v w => Disjoint (A v).ζ.source (A w).ζ.source) ∧
      (∀ v : originalPositiveFiber N g 0, ε < r v ^ ((v : Place ℂ F).ord g).toNat) ∧
      ∀ P : Place ℂ F, g ∈ P.toValuationSubring → ‖originalPlaceEval N ℂ P g‖ < ε →
        ∃ v : originalPositiveFiber N g 0, P ∈ (A v).ζ.source := by
  classical
  have hg0 : g ≠ 0 := by simpa using hg 0
  let S := originalPositiveFiber N g 0
  have hS : ∀ v ∈ S, g ∈ v.toValuationSubring ∧ originalPlaceEval N ℂ v g = 0 := by
    intro v hv
    have ho : 0 < v.ord g := by simpa using (mem_originalPositiveFiber N g 0 v).mp hv
    have hm := v.mem_of_ord_nonneg ho.le
    exact ⟨hm, (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v hm hg0).mpr ho⟩
  obtain ⟨A, r, m, hm, hA, hd, hscale⟩ := exists_finite_original_normal_coordinates hg0 S hS
  let U : Place ℂ F → Set (Place ℂ F) := fun v =>
    if hv : v ∈ S then (A ⟨v, hv⟩).ζ.source else ∅
  have hU : ∀ v ∈ S, IsOpen (U v) := by
    intro v hv
    simpa only [U, dif_pos hv] using (A ⟨v, hv⟩).ζ.open_source
  have hvU : ∀ v ∈ S, v ∈ U v := by
    intro v hv
    simpa only [U, dif_pos hv] using (hA ⟨v, hv⟩).2.1
  obtain ⟨δ, hδ, hcover⟩ := OriginalChart.exists_original_prescribed_fiber_cover N 0
    (by simpa using hg0) S (mem_originalPositiveFiber N g 0) U hU hvU
  let ε := min δ (m / 2)
  have hε : 0 < ε := lt_min hδ (half_pos hm)
  refine ⟨A, r, ε, hε, hA, hd, ?_, ?_⟩
  · intro v
    exact (min_le_right δ (m / 2)).trans_lt ((half_lt_self hm).trans_le (hscale v))
  · intro P hP hsmall
    have hne : g - algebraMap ℂ F (originalPlaceEval N ℂ P g) ≠ 0 :=
      sub_ne_zero.mpr (hg _)
    have hmem := sub_mem hP (P.algebraMap_mem' (originalPlaceEval N ℂ P g))
    have hord : 0 < P.ord (g - algebraMap ℂ F (originalPlaceEval N ℂ P g)) := by
      apply (originalPlaceEval_eq_zero_iff_ord_pos N ℂ P hmem hne).mp
      rw [originalPlaceEval_sub_algebraMap N ℂ P hP, sub_self]
    obtain ⟨v, hv, hPv⟩ := hcover (originalPlaceEval N ℂ P g)
      (by simpa only [dist_zero_right] using hsmall.trans_le (min_le_left δ (m / 2))) P hord
    refine ⟨⟨v, hv⟩, ?_⟩
    simpa only [U, dif_pos hv] using hPv

end
end Dubon2026.SourceFunctionField.CellGeometry
