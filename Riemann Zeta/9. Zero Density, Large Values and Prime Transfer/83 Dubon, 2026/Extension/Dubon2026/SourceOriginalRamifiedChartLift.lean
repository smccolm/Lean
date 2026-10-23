import Dubon2026.SourceOriginalRamifiedPlaceContinuity

/-! DUB-17/18 -> original Picard-period Hecke comparison -> reverse
period-lattice inclusion. Every actual chart at an analytic place admits
local upper-half-plane lifts converging to its chosen center. Only
continuity at that center is needed: arbitrary chosen roots need not
be continuous elsewhere. Existing normalized chart comparison and its
inverse theorem handle elliptic ramification without excluding points.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve Filter Metric EllipticCoordinate
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem powerDescent_root_continuousAt_zero (n : ℕ) (hn : n ≠ 0) :
    ContinuousAt (PowerDescent.root n hn) (0 : ℂ) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε ^ n, pow_pos hε _, fun z hz => ?_⟩
  rw [PowerDescent.root_zero, dist_zero_right] at ⊢
  rw [dist_zero_right] at hz
  apply (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le hn).mp
  rwa [← norm_pow, PowerDescent.root_pow]

theorem exists_original_chart_analytic_lift (τ : ℍ) :
    ∃ r : ℂ → ℂ, Tendsto r (𝓝 (0 : ℂ)) (𝓝 (τ : ℂ)) ∧
      ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
        originalAnalyticPlace N (ofComplex (r z)) = placeFamily N (originalAnalyticPlace N τ) z := by
  obtain ⟨δ, hδ, ho⟩ := originalRamifiedPlace_chart_orders N τ
  let v := originalAnalyticPlace N τ
  let S : ComparisonData N :=
    { γ := placeFamily N v
      γ' := originalRamifiedPlace N τ
      v := v
      U := ball 0 (placeRadius N v)
      U' := ball 0 δ
      z₀ := 0
      z₀' := 0
      hU := ball_mem_nhds 0 (place_spec N v).1
      hU' := ball_mem_nhds 0 hδ
      h₀ := (originalRamifiedPlace_zero N τ).trans (place_spec N v).2.1.symm
      ht := (place_spec N v).2.2.2
      hγ := (place_spec N v).2.2.1
      hγ' := ho }
  have hT : AnalyticAt ℂ S.transition 0 := S.analyticAt_transition
  have hT0 : S.transition 0 = 0 := S.transition_self
  have hd : deriv S.transition 0 ≠ 0 := S.deriv_transition_ne_zero
  let r := hT.hasStrictDerivAt.localInverse S.transition (deriv S.transition 0) 0 hd
  have hr : AnalyticAt ℂ r 0 := by simpa only [hT0] using hT.analyticAt_localInverse hd
  have hr0 : r 0 = 0 := by
    simpa only [hT0] using
      (HasStrictDerivAt.eventually_left_inverse hT.hasStrictDerivAt hd).self_of_nhds
  have hrt : Tendsto r (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hr0] using hr.continuousAt.tendsto
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), S.transition (r z) = z := by
    simpa only [hT0] using HasStrictDerivAt.eventually_right_inverse hT.hasStrictDerivAt hd
  let e := originalAnalyticRamification N τ
  let hne := (originalAnalyticRamification_pos N τ).ne'
  let u := fun z => PowerDescent.root e hne (r z)
  have hu : Tendsto u (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hroot := (powerDescent_root_continuousAt_zero e hne).tendsto
    rw [PowerDescent.root_zero] at hroot
    exact hroot.comp hrt
  refine ⟨fun z => param τ (u z), ?_, ?_⟩
  · have hp := (hasDerivAt_param τ).continuousAt.tendsto
    rw [param_zero] at hp
    exact hp.comp hu
  · filter_upwards [hrt.eventually S.eventually_place_eq, he] with z hz hze
    change originalRamifiedPlace N τ (r z) = placeFamily N v z
    exact hz.trans (congrArg (placeFamily N v) hze)

end
end Dubon2026.SourceFunctionField.OriginalChart
