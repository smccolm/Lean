import Dubon2026.SourceCurveAnalyticChartDifferenceOrders

/-! DUB-17/18 -> auxiliary cover Abel comparison -> chart branch compatibility.
Adapt the existing original-curve uniformizer-division and meromorphic
identity argument to the actual cover residue evaluation and place orders.
The original proof was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex. -/
namespace Dubon2026.SourceCurve.AnalyticChart.ComparisonData
noncomputable section
open Filter
open scoped Topology
variable {EE : Type*} [Field EE] [Algebra ℂ EE]
variable {hv : ∀ P : Place ℂ EE, Function.Bijective (algebraMap ℂ P.ResidueField)}
variable (S : ComparisonData hv)

theorem deriv_transition_ne_zero : deriv S.transition S.z₀' ≠ 0 := by
  let g : ℂ → ℂ := fun u => S.transition u - S.z₀
  have hg : AnalyticAt ℂ g S.z₀' := S.analyticAt_transition.sub analyticAt_const
  have ha : analyticOrderAt g S.z₀' = (1 : ℕ∞) := by
    apply WithTop.map_injective (Nat.cast_injective (R := ℤ))
    change (analyticOrderAt g S.z₀').map (Nat.cast : ℕ → ℤ) = (1 : ℕ∞).map (Nat.cast : ℕ → ℤ)
    rw [← hg.meromorphicOrderAt_eq, S.order_transition]
    rfl
  have hd := hg.deriv.analyticOrderAt_eq_zero.mp
    (analyticOrderAt_deriv_of_pos hg (n := 0) (by simpa only [Nat.cast_zero, zero_add] using ha))
  simpa only [g, deriv_sub_const] using hd

theorem eventually_good : ∀ᶠ u in 𝓝 S.z₀',
    u ∈ S.U' ∧ S.transition u ∈ S.U ∧ AnalyticAt ℂ S.transition u ∧ deriv S.transition u ≠ 0 := by
  filter_upwards [S.hU', S.tendsto_transition.eventually S.hU,
    S.analyticAt_transition.eventually_analyticAt,
    S.analyticAt_transition.deriv.continuousAt.eventually_ne S.deriv_transition_ne_zero]
    with u hu hu' ha hd
  exact ⟨hu, hu', ha, hd⟩

theorem meromorphicAt_difference {f : EE} (hf : f ≠ 0)
    {u : ℂ} (hu' : u ∈ S.U') (hu : S.transition u ∈ S.U) (ha : AnalyticAt ℂ S.transition u) :
    MeromorphicAt (S.difference f) u :=
  (S.hγ' u hu' f hf).1.sub ((S.hγ (S.transition u) hu f hf).1.comp_analyticAt ha)

theorem ord_eq_of_difference_order_top {f : EE} (hf : f ≠ 0)
    {u : ℂ} (hu' : u ∈ S.U') (hu : S.transition u ∈ S.U)
    (ha : AnalyticAt ℂ S.transition u) (hd : deriv S.transition u ≠ 0)
    (ht : meromorphicOrderAt (S.difference f) u = ⊤) :
    (S.γ' u).ord f = (S.γ (S.transition u)).ord f := by
  have hev : (fun w => (S.γ' w).rationalEval (hv (S.γ' w)) f) =ᶠ[𝓝[≠] u]
      (fun w => (S.γ w).rationalEval (hv (S.γ w)) f) ∘ S.transition :=
    (meromorphicOrderAt_eq_top_iff.mp ht).mono fun _ hw => sub_eq_zero.mp hw
  have h := meromorphicOrderAt_congr hev
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero ha hd,
    (S.hγ' u hu' f hf).2.1, (S.hγ (S.transition u) hu f hf).2.1] at h
  exact WithTop.coe_injective h

theorem eventually_place_eq : ∀ᶠ u in 𝓝 S.z₀', S.γ' u = S.γ (S.transition u) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp S.eventually_good
  filter_upwards [Metric.ball_mem_nhds S.z₀' hr] with u hu
  obtain ⟨hu', huU, ha, hd⟩ := hball u hu
  have hord : ∀ f : EE, f ≠ 0 →
      (S.γ' u).ord f = (S.γ (S.transition u)).ord f := by
    intro f hf
    apply S.ord_eq_of_difference_order_top hf hu' huU ha hd
    by_contra hne
    have hOn : MeromorphicOn (S.difference f) (Metric.ball S.z₀' r) := fun w hw =>
      S.meromorphicAt_difference hf (hball w hw).1 (hball w hw).2.1 (hball w hw).2.2.1
    exact hOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball S.z₀' r).isPreconnected hu (Metric.mem_ball_self hr) hne (S.difference_order_top f)
  apply Place.ext
  apply SetLike.ext
  intro f
  by_cases hf : f = 0
  · subst f
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · rw [(S.γ' u).mem_iff_ord_nonneg, (S.γ (S.transition u)).mem_iff_ord_nonneg, hord f hf]

end
end Dubon2026.SourceCurve.AnalyticChart.ComparisonData
