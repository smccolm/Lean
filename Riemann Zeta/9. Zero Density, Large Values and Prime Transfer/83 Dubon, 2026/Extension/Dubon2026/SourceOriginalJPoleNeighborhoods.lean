import Dubon2026.SourceOriginalNormalFiberNeighborhoods

/-! DUB-17/18 -> geometric dissection -> neighborhoods of the poles of j.
Apply the actual normal-fiber theorem to the reciprocal of j. Its zero
fiber is exactly the original pole set. The exact evaluation-inverse law
turns the uniform small reciprocal bound into exhaustion at large j values.
No additional pole-chart or exhaustion premise is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
open scoped Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_j_pole_neighborhoods :
    ∃ (A : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 → AnalyticCoord N)
      (r : originalPositiveFiber N (jOver N ℂ)⁻¹ 0 → ℝ) (R : ℝ), 0 < R ∧
      (∀ v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0,
        jOver N ℂ ∉ (v : Place ℂ F).toValuationSubring ∧
        0 < r v ∧ (v : Place ℂ F) ∈ (A v).ζ.source ∧ (A v).ζ v = 0 ∧
        (A v).ζ.target = Metric.ball 0 (r v) ∧
        (A v).ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) (v : Place ℂ F)).source ∧
        0 < ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat ∧
        ∀ P ∈ (A v).ζ.source, (jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
          originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ =
            ((A v).ζ P) ^ ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat) ∧
      (Pairwise fun v w => Disjoint (A v).ζ.source (A w).ζ.source) ∧
      ∀ P : Place ℂ F, jOver N ℂ ∈ P.toValuationSubring →
        R ≤ ‖originalPlaceEval N ℂ P (jOver N ℂ)‖ →
        ∃ v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0, P ∈ (A v).ζ.source := by
  have hj0 : jOver N ℂ ≠ 0 := fun h => transcendental_jOver N ℂ (h ▸ isAlgebraic_zero)
  have hi : ∀ c : ℂ, (jOver N ℂ)⁻¹ ≠ algebraMap ℂ F c := by
    intro c h
    have ha : IsAlgebraic ℂ ((jOver N ℂ)⁻¹) := h ▸ isAlgebraic_algebraMap c
    exact transcendental_jOver N ℂ (by simpa only [inv_inv] using ha.inv)
  obtain ⟨A, r, ε, hε, hA, hd, _, hcover⟩ := exists_original_normal_fiber_neighborhoods hi
  let R := ε⁻¹ + 1
  have hR : 0 < R := add_pos (inv_pos.mpr hε) one_pos
  refine ⟨A, r, R, hR, ?_, hd, ?_⟩
  · intro v
    refine ⟨?_, hA v⟩
    have hp := (mem_originalPositiveFiber N (jOver N ℂ)⁻¹ 0 v).mp v.2
    simp only [map_zero, sub_zero, Place.ord_inv] at hp
    exact fun hv => (not_lt_of_ge (v.1.ord_nonneg_of_mem hv)) (by omega)
  · intro P hP hlarge
    have hvalne : originalPlaceEval N ℂ P (jOver N ℂ) ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hlarge
      exact (not_le_of_gt hR) hlarge
    have hord : P.ord (jOver N ℂ) = 0 := by
      have hnonneg := P.ord_nonneg_of_mem hP
      have hnotpos : ¬ 0 < P.ord (jOver N ℂ) := fun hp => hvalne
        ((originalPlaceEval_eq_zero_iff_ord_pos N ℂ P hP hj0).mpr hp)
      omega
    have hinv : (jOver N ℂ)⁻¹ ∈ P.toValuationSubring :=
      P.mem_of_ord_nonneg (by rw [Place.ord_inv, hord, neg_zero])
    apply hcover P hinv
    rw [originalPlaceEval_inv, norm_inv]
    apply inv_lt_of_inv_lt₀ hε
    exact (lt_add_one ε⁻¹).trans_le hlarge

end
end Dubon2026.SourceFunctionField.CellGeometry
