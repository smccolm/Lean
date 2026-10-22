import Dubon2026.SourceOriginalOnePoleFunction
import Dubon2026.SourceOriginalEvaluationContinuity
import Dubon2026.SourceOriginalComplexCompact
import Mathlib.Analysis.Complex.AbsMax

/-! DUB-17/18 -> original torsion cardinality -> connected complex curve.
A proper clopen component would make a nonconstant original function,
regular away from a place in the other component, attain an interior
maximum of its norm. Native maximum modulus gives local constancy.
The proved exact original chart order then contradicts the finite order
of that nonzero original function minus its constant value.
This shortens the external argument by avoiding a separate infinite-zero
construction. Compactness and all order inputs are derived for the original curve.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem original_false_of_proper_clopen :
    letI := placeTopology N
    ∀ U : Set (Place ℂ (modularFunctionFieldOver N ℂ)), IsClopen U →
      ∀ v ∈ U, Uᶜ.Nonempty → False := by
  letI := placeTopology N
  letI := place_compactSpace N
  intro U hU v hv hne
  obtain ⟨f, hfc, hfreg⟩ := exists_original_nonconstant_regular_away N v
  have hreg : ∀ w ∈ Uᶜ, f ∈ w.toValuationSubring :=
    fun w hw => hfreg w (fun h => hw (h ▸ hv))
  have hcont : ContinuousOn (fun w => ‖originalPlaceEval N ℂ w f‖) Uᶜ :=
    fun w hw => ((continuousAt_originalPlaceEval N w (hreg w hw)).norm).continuousWithinAt
  obtain ⟨w, hw, hmax⟩ := hU.compl.isClosed.isCompact.exists_isMaxOn hne hcont
  have hloc : IsLocalMax (fun w => ‖originalPlaceEval N ℂ w f‖) w :=
    hmax.isLocalMax (hU.compl.isOpen.mem_nhds hw)
  let G : ℂ → ℂ := fun z => originalPlaceEval N ℂ (placeFamily N w z) f
  have hloc' : IsLocalMax (norm ∘ G) 0 := by
    have h : IsLocalMax (fun w => ‖originalPlaceEval N ℂ w f‖) (placeFamily N w 0) := by
      rw [(place_spec N w).2.1]
      exact hloc
    exact h.comp_tendsto (placeFamily_continuousAt_zero N w)
  have han : AnalyticAt ℂ G 0 := analyticAt_place_reading N w (hreg w hw)
  have hconst := Complex.eventually_eq_of_isLocalMax_norm
    (han.eventually_analyticAt.mono fun z hz => hz.differentiableAt) hloc'
  have hdiff : f - algebraMap ℂ (modularFunctionFieldOver N ℂ) (G 0) ≠ 0 :=
    fun h => hfc ⟨G 0, (sub_eq_zero.mp h).symm⟩
  have hreg0 : f ∈ (placeFamily N w 0).toValuationSubring := by
    rw [(place_spec N w).2.1]
    exact hreg w hw
  have ho := (place_spec N w).2.2.1.meromorphicOrderAt_sub_const
    (ball_mem_nhds 0 (place_spec N w).1) hreg0 (G 0) hdiff
  have htop : meromorphicOrderAt (fun z => G z - G 0) 0 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hconst.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  change meromorphicOrderAt (fun z => G z - G 0) 0 = _ at ho
  rw [htop] at ho
  exact WithTop.top_ne_coe ho

end
end Dubon2026.SourceFunctionField.OriginalChart
