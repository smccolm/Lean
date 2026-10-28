import Dubon2026.SourceMeromorphicPrimitiveMultiplier

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
actual meromorphic function -> nonzero translated cusp limits. The actual
weight-two differential decay rules out poles high in each cusp. Its
primitive has a uniform limit, and the actual function is a nonzero constant
times its exponential. The analytic differential input remains. -/
namespace Dubon2026.SourceMeromorphicPrimitiveMultiplier
noncomputable section
open scoped MatrixGroups Topology ModularForm
open UpperHalfPlane Filter Set Metric

section Analytic

variable {m : ℍ → ℤ} {ω : ℍ → ℂ}
  (hres : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
    (m τ = 0 → ω τ = g τ))
include hres

theorem analyticAt_omega (τ : ℍ) (hm : m τ = 0) :
    AnalyticAt ℂ (fun z => ω (ofComplex z)) τ := by
  obtain ⟨g, hg, hexp, hval⟩ := hres τ
  refine hg.congr ?_
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), g z = ω (ofComplex z) := by
    filter_upwards [hexp] with z hz
    rw [hz, hm]
    simp
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with z hz
  by_cases hzτ : z = τ
  · subst hzτ
    rw [ofComplex_apply]
    exact (hval hm).symm
  · exact hz hzτ

theorem tendsto_norm_omega_atTop (τ : ℍ) (hm : m τ ≠ 0) :
    Tendsto (fun z => ‖ω (ofComplex z)‖) (𝓝[≠] (τ : ℂ)) atTop := by
  obtain ⟨g, hg, hexp, -⟩ := hres τ
  have h1 : Tendsto (fun z => (z - τ) * ω (ofComplex z)) (𝓝[≠] (τ : ℂ)) (𝓝 (m τ : ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ => (m τ : ℂ) + (z - τ) * g z) τ :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hg.continuousAt)
    have h2 := hc.tendsto
    simp only [sub_self, zero_mul, add_zero] at h2
    refine (h2.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hexp, self_mem_nhdsWithin] with z hz hzτ
    rw [hz, mul_add, mul_div_cancel₀ _ (sub_ne_zero.mpr hzτ)]
  have h3 := h1.norm
  have h4 : Tendsto (fun z : ℂ => ‖z - τ‖⁻¹) (𝓝[≠] (τ : ℂ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE (τ : ℂ))
  have hpos : 0 < ‖(m τ : ℂ)‖ := norm_pos_iff.mpr (Int.cast_ne_zero.mpr hm)
  refine (h3.pos_mul_atTop hpos h4).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hzτ
  have hne : ‖z - ↑τ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzτ)
  rw [norm_mul]
  field_simp

end Analytic

/-- An explicit exponential bound for the actual translated weight-two differential. -/
structure CuspBound (ω : ℍ → ℂ) (σ : SL(2, ℤ)) (C δ A₀ : ℝ) : Prop where
  δ_pos : 0 < δ
  C_nonneg : 0 ≤ C
  A₀_pos : 0 < A₀
  bound : ∀ τ : ℍ, A₀ ≤ τ.im → ‖(ω ∣[(2 : ℤ)] σ) τ‖ ≤ C * Real.exp (-δ * τ.im)

theorem exists_cuspBound {ω : ℍ → ℂ} {σ : SL(2, ℤ)}
    (hcusp : ∃ δ : ℝ, 0 < δ ∧
      (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) :
    ∃ C δ A₀, CuspBound ω σ C δ A₀ := by
  obtain ⟨δ, hδ, hO⟩ := hcusp
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine ⟨max C 0, δ, max A 1, hδ, le_max_right _ _, by positivity, fun τ hτ => ?_⟩
  have h : ‖(ω ∣[(2 : ℤ)] σ) τ‖ ≤ C * ‖Real.exp (-δ * τ.im)‖ := hA τ ((le_max_left _ _).trans hτ)
  rw [Real.norm_eq_abs, Real.abs_exp] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem continuous_denom (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => denom g z) := by
  simp only [denom]
  fun_prop

theorem differentiableAt_denom (g : GL (Fin 2) ℝ) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => denom g w) z := by
  simp only [denom]
  fun_prop


end
end Dubon2026.SourceMeromorphicPrimitiveMultiplier
