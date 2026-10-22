import Dubon2026.SourceOriginalComplexCompact
import Dubon2026.SourceOriginalEvaluationContinuity

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> locate all nearby fibers inside prescribed chart disks.
The earlier finite-fiber cover proves compactness. Here that established
compactness bounds the reciprocal off any specified neighborhoods of the
central fiber, avoiding another analytic preimage-count construction.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem exists_original_prescribed_fiber_cover {f : F} (t₀ : ℂ)
    (hne : f - algebraMap ℂ F t₀ ≠ 0)
    (Z₀ : Finset (Place ℂ F)) (hZ₀ : ∀ v, v ∈ Z₀ ↔ 0 < v.ord (f - algebraMap ℂ F t₀))
    (U : Place ℂ F → Set (Place ℂ F)) (hU : ∀ v ∈ Z₀, IsOpen (U v))
    (hvU : ∀ v ∈ Z₀, v ∈ U v) :
    ∃ ε > 0, ∀ t : ℂ, dist t t₀ < ε → ∀ w : Place ℂ F,
      0 < w.ord (f - algebraMap ℂ F t) → ∃ v ∈ Z₀, w ∈ U v := by
  letI := place_compactSpace N
  let g₀ := f - algebraMap ℂ F t₀
  let u := g₀⁻¹
  let Kc : Set (Place ℂ F) := (⋃ v ∈ Z₀, U v)ᶜ
  have hKcl : IsClosed Kc := (isOpen_biUnion fun v hv => hU v hv).isClosed_compl
  have hureg : ∀ w ∈ Kc, u ∈ w.toValuationSubring := by
    intro w hw
    have hwZ : w ∉ Z₀ := fun hwZ => hw (Set.mem_biUnion (Finset.mem_coe.2 hwZ) (hvU w hwZ))
    have hord : ¬ 0 < w.ord g₀ := fun h => hwZ ((hZ₀ w).mpr h)
    apply w.mem_of_ord_nonneg
    rw [show u = g₀⁻¹ from rfl, w.ord_inv]
    omega
  have hcont : ContinuousOn (fun w => originalPlaceEval N ℂ w u) Kc :=
    fun w hw => (continuousAt_originalPlaceEval N w (hureg w hw)).continuousWithinAt
  obtain ⟨M, hM⟩ := hKcl.isCompact.exists_bound_of_continuousOn hcont
  refine ⟨1 / (|M| + 1), by positivity, ?_⟩
  intro t ht w hw
  by_contra hcon
  push Not at hcon
  have hwK : w ∈ Kc := by
    simp only [Kc, mem_compl_iff, mem_iUnion, not_exists]
    exact fun v hv => hcon v hv
  have hfw : f ∈ w.toValuationSubring :=
    (original_sub_const_mem_iff N w f t).mp (w.mem_of_ord_nonneg hw.le)
  have hgmem : g₀ ∈ w.toValuationSubring := sub_mem hfw (w.algebraMap_mem' t₀)
  have hval : originalPlaceEval N ℂ w g₀ = t - t₀ := by
    rw [show g₀ = f - algebraMap ℂ F t₀ from rfl,
      originalPlaceEval_sub_algebraMap N ℂ w hfw,
      originalPlaceEval_eq_of_ord_sub_pos N ℂ w f t hw]
  have hprod : originalPlaceEval N ℂ w g₀ * originalPlaceEval N ℂ w u = 1 := by
    rw [originalPlaceEval_of_mem N ℂ w hgmem, originalPlaceEval_of_mem N ℂ w (hureg w hwK),
      ← map_mul]
    have he : (⟨g₀, hgmem⟩ : w.toValuationSubring) * ⟨u, hureg w hwK⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hne)
    rw [he, map_one]
  have hbound : ‖originalPlaceEval N ℂ w u‖ ≤ |M| := (hM w hwK).trans (le_abs_self M)
  have h1 : (1 : ℝ) ≤ ‖t - t₀‖ * |M| := by
    calc 1 = ‖originalPlaceEval N ℂ w g₀ * originalPlaceEval N ℂ w u‖ := by rw [hprod, norm_one]
      _ = ‖t - t₀‖ * ‖originalPlaceEval N ℂ w u‖ := by rw [norm_mul, hval]
      _ ≤ ‖t - t₀‖ * |M| := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  rw [dist_eq_norm] at ht
  have h2 : ‖t - t₀‖ * |M| < 1 := by
    calc ‖t - t₀‖ * |M| ≤ (1 / (|M| + 1)) * |M| :=
        mul_le_mul_of_nonneg_right ht.le (abs_nonneg M)
      _ < 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
        linarith
  linarith

end
end Dubon2026.SourceFunctionField.OriginalChart
