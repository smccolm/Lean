import Mathlib

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> invariant
comparison V -> removable filling of the locally finite smooth dipole product.
The input is a punctured integer-order local model with a nonvanishing C1
factor. It is weaker than the required globally invariant comparison V.
Meromorphic normal forms cannot be substituted because these factors are C1.
No period identity or original meromorphic realization is assumed. -/
namespace Dubon2026.SourceSmoothLocalModel
noncomputable section
open Filter Complex Set
open scoped Topology

section Regularize

open scoped Classical

/-- Fill an existing punctured finite limit; retain zero at a genuine pole. -/
def regularize (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h : ∃ c, Tendsto f (𝓝[≠] z) (𝓝 c) then h.choose else 0

theorem regularize_eq_of_tendsto {f : ℂ → ℂ} {z c : ℂ} (h : Tendsto f (𝓝[≠] z) (𝓝 c)) :
    regularize f z = c := by
  have hex : ∃ c, Tendsto f (𝓝[≠] z) (𝓝 c) := ⟨c, h⟩
  rw [regularize, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

theorem regularize_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : ¬ ∃ c, Tendsto f (𝓝[≠] z) (𝓝 c)) :
    regularize f z = 0 := by
  rw [regularize, dif_neg h]

theorem not_tendsto_of_neg {Ψ : ℂ → ℂ} {τ : ℂ} {k : ℤ} (hk : k < 0) (hΨ : ContinuousAt Ψ τ)
    (hΨ0 : Ψ τ ≠ 0) : ¬ ∃ c, Tendsto (fun z => (z - τ) ^ k * Ψ z) (𝓝[≠] τ) (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h1 : Tendsto (fun z : ℂ => z - τ) (𝓝[≠] τ) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z : ℂ => z - τ) (𝓝 τ) (𝓝 (τ - τ)) :=
        (continuous_id.sub continuous_const).continuousAt.tendsto
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 hz
  have h2 : Tendsto (fun z : ℂ => ‖(z - τ) ^ k‖) (𝓝[≠] τ) atTop :=
    by simpa [Function.comp_def] using
      (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded hk)).comp h1
  have h3 : Tendsto (fun z => ‖Ψ z‖) (𝓝[≠] τ) (𝓝 ‖Ψ τ‖) :=
    (hΨ.norm.tendsto).mono_left nhdsWithin_le_nhds
  have h4 : Tendsto (fun z => ‖(z - τ) ^ k‖ * ‖Ψ z‖) (𝓝[≠] τ) atTop :=
    h2.atTop_mul_pos (norm_pos_iff.2 hΨ0) h3
  have h5 : Tendsto (fun z => ‖(z - τ) ^ k * Ψ z‖) (𝓝[≠] τ) (𝓝 ‖c‖) := hc.norm
  simp_rw [norm_mul] at h5
  exact not_tendsto_atTop_of_tendsto_nhds h5 h4

theorem regularize_eventuallyEq {f Ψ : ℂ → ℂ} {τ : ℂ} {k : ℤ}
    (hf : ∀ᶠ z in 𝓝[≠] τ, f z = (z - τ) ^ k * Ψ z) (hΨ : ∀ᶠ z in 𝓝 τ, ContinuousAt Ψ z)
    (hΨ0 : Ψ τ ≠ 0) : regularize f =ᶠ[𝓝 τ] fun z => (z - τ) ^ k * Ψ z := by
  rw [eventually_nhdsWithin_iff] at hf
  obtain ⟨O, hO, hOo, hτO⟩ := _root_.mem_nhds_iff.1 (hf.and hΨ)
  have hmem : O ∈ 𝓝 τ := hOo.mem_nhds hτO
  filter_upwards [hmem] with w hw
  by_cases hwτ : w = τ
  · subst hwτ
    have hf' : ∀ᶠ z in 𝓝[≠] w, f z = (z - w) ^ k * Ψ z :=
      eventually_nhdsWithin_iff.2 (Filter.mem_of_superset hmem fun z hz => (hO hz).1)
    rcases lt_or_ge k 0 with hk | hk
    · rw [regularize_eq_zero, sub_self, zero_zpow k hk.ne, zero_mul]
      intro ⟨c, hc⟩
      exact not_tendsto_of_neg hk (hO hw).2 hΨ0 ⟨c, hc.congr' hf'⟩
    · apply regularize_eq_of_tendsto
      refine Tendsto.congr' (EventuallyEq.symm hf') ?_
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : ContinuousAt (fun z => (z - w) ^ k * Ψ z) w := by
        refine ContinuousAt.mul ?_ (hO hw).2
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
        simp only [zpow_natCast]
        exact ((continuousAt_id.sub continuousAt_const).pow m)
      exact hc.tendsto
  · apply regularize_eq_of_tendsto
    have hne : ∀ᶠ z in 𝓝 w, z ≠ τ := isOpen_ne.mem_nhds hwτ
    have hf' : f =ᶠ[𝓝 w] fun z => (z - τ) ^ k * Ψ z := by
      filter_upwards [hOo.mem_nhds hw, hne] with z hz hzτ using (hO hz).1 hzτ
    have hc : ContinuousAt (fun z => (z - τ) ^ k * Ψ z) w :=
      ContinuousAt.mul ((continuousAt_id.sub continuousAt_const).zpow₀ k
        (Or.inl (sub_ne_zero.2 hwτ))) (hO hw).2
    have hc' : Tendsto f (𝓝 w) (𝓝 ((w - τ) ^ k * Ψ w)) := hc.tendsto.congr' hf'.symm
    exact hc'.mono_left nhdsWithin_le_nhds

theorem eventually_continuousAt {Ψ : ℂ → ℂ} {τ : ℂ} (h : ContDiffAt ℝ 1 Ψ τ) :
    ∀ᶠ z in 𝓝 τ, ContinuousAt Ψ z :=
  (h.eventually (by simp)).mono fun _ hz => hz.continuousAt

theorem contDiffAt_zpow {Ψ : ℂ → ℂ} {τ : ℂ} (h : ContDiffAt ℝ 1 Ψ τ) (h0 : Ψ τ ≠ 0) (k : ℤ) :
    ContDiffAt ℝ 1 (fun z => Ψ z ^ k) τ := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · simp only [zpow_natCast]; exact h.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (h.pow m).inv (pow_ne_zero _ h0)

end Regularize
end
end Dubon2026.SourceSmoothLocalModel
