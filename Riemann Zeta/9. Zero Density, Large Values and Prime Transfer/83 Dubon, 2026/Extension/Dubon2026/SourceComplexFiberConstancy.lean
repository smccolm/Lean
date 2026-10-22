import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi ->
principal-divisor kernel -> local constancy of the weighted fiber sum.
These analytic and finite-sum inputs are used by that exact fiber argument.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.ComplexFiberContour
noncomputable section
open Filter Complex Metric
open scoped Topology

theorem eventually_forall_sphere_ne {R : ℂ → ℂ} {c t₀ : ℂ} {r : ℝ}
    (hcont : ContinuousOn R (Metric.sphere c r)) (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t₀) :
    ∀ᶠ t in 𝓝 t₀, ∀ z ∈ Metric.sphere c r, R z ≠ t := by
  rcases (Metric.sphere c r).eq_empty_or_nonempty with hemp | hnonempty
  · exact Filter.Eventually.of_forall fun t z hz => by simp [hemp] at hz
  have hc' : ContinuousOn (fun z => ‖R z - t₀‖) (Metric.sphere c r) :=
    (hcont.sub continuousOn_const).norm
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hnonempty hc'
  set δ := ‖R z₁ - t₀‖ with hδ
  have hδpos : 0 < δ := norm_pos_iff.2 (sub_ne_zero.2 (hne z₁ hz₁))
  filter_upwards [Metric.ball_mem_nhds t₀ hδpos] with t ht z hz hzt
  have hle : δ ≤ ‖R z - t₀‖ := isMinOn_iff.1 hmin z hz
  rw [hzt] at hle
  rw [Metric.mem_ball, dist_eq_norm] at ht
  linarith

theorem eq_of_hasDerivAt_zero_off_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {L L' : ℂ → E} {t₀ : ℂ} {ε : ℝ}
    (hL : ∀ t ∈ Metric.ball t₀ ε, HasDerivAt L (L' t) t)
    (h0 : ∀ t ∈ Metric.ball t₀ ε, t ≠ t₀ → L' t = 0) :
    ∀ t ∈ Metric.ball t₀ ε, L t = L t₀ := by
  intro t ht
  have hε : 0 < ε := Metric.pos_of_mem_ball ht
  have hdiff : DifferentiableOn ℂ L (Metric.ball t₀ ε) := fun s hs =>
    (hL s hs).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ Metric.ball t₀ ε, deriv L s = L' s := fun s hs => (hL s hs).deriv
  have hA : AnalyticAt ℂ L t₀ := hdiff.analyticAt (Metric.ball_mem_nhds t₀ hε)
  have hc : ContinuousAt (deriv L) t₀ := hA.deriv.continuousAt
  have hd0 : deriv L t₀ = 0 := by
    have h1 : Filter.Tendsto (deriv L) (𝓝[≠] t₀) (𝓝 (deriv L t₀)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[≠] t₀, deriv L s = 0 := by
      have hb : ∀ᶠ s in 𝓝 t₀, s ∈ Metric.ball t₀ ε := Metric.ball_mem_nhds t₀ hε
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds hb, self_mem_nhdsWithin]
        with s hs hs'
      rw [hderiv s hs, h0 s hs hs']
    have h2 : Filter.Tendsto (deriv L) (𝓝[≠] t₀) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun s hs => hs.symm)
    exact tendsto_nhds_unique h1 h2
  have hEq : Set.EqOn (deriv L) 0 (Metric.ball t₀ ε) := by
    intro s hs
    by_cases hst : s = t₀
    · rw [hst]; exact hd0
    · rw [hderiv s hs, h0 s hs hst]; rfl
  exact IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball t₀ ε).isPreconnected
    hdiff hEq ht (Metric.mem_ball_self hε)

theorem sum_eq_sum_sum {α β γ M : Type*} [AddCommMonoid M]
    (S : Finset α) (Z₀ : Finset β) (Zf : β → Finset γ) (sy : β → γ → α)
    (hsurj : ∀ w ∈ S, ∃ v ∈ Z₀, ∃ a ∈ Zf v, sy v a = w)
    (hmem : ∀ v ∈ Z₀, ∀ a ∈ Zf v, sy v a ∈ S)
    (hinj : ∀ v ∈ Z₀, ∀ v' ∈ Z₀, ∀ a ∈ Zf v, ∀ a' ∈ Zf v', sy v a = sy v' a' → v = v' ∧ a = a')
    (cf : α → M) :
    ∑ w ∈ S, cf w = ∑ v ∈ Z₀, ∑ a ∈ Zf v, cf (sy v a) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => sy x.1 x.2) ?_ ?_ ?_ ?_
  · rintro ⟨v, a⟩ hx
    obtain ⟨hv, ha⟩ := Finset.mem_sigma.1 hx
    exact hmem v hv a ha
  · rintro ⟨v, a⟩ hx ⟨v', a'⟩ hx' h
    obtain ⟨hv, ha⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hv', ha'⟩ := Finset.mem_sigma.1 hx'
    obtain ⟨rfl, rfl⟩ := hinj v hv v' hv' a ha a' ha' h
    rfl
  · intro w hw
    obtain ⟨v, hv, a, ha, rfl⟩ := hsurj w hw
    exact ⟨⟨v, a⟩, Finset.mem_sigma.2 ⟨hv, ha⟩, rfl⟩
  · intros; rfl


end
end Dubon2026.SourceFunctionField.ComplexFiberContour
