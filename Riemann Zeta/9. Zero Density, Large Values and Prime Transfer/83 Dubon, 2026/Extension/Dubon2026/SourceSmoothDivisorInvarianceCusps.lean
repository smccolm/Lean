import Dubon2026.SourceSmoothDivisorLocalOrders

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
Removable filling preserves actual subgroup invariance, and the proved height
bound makes the product equal one sufficiently high after every integral
translate. The source cusp condition is derived from the compact dipoles;
neither global invariance nor cusp normalization of V is an input.
Adapted from the pinned Apache-2.0 scope-889 construction. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Metric
open SourceSmoothProjective SourceSmoothLocalModel
open scoped MatrixGroups Topology Real Classical
namespace Data
variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

theorem tendsto_sm_nhdsNE (γ : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto (sm γ) (𝓝[≠] τ) (𝓝[≠] (sm γ τ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuousAt_sm γ hτ).tendsto.mono_left nhdsWithin_le_nhds) ?_
  have hU : ∀ᶠ z in 𝓝 τ, 0 < z.im := (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hτ
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hzτ
  exact fun h => hzτ (sm_inj γ hz hτ h)

theorem tendsto_of_tendsto_sm {f : ℂ → ℂ} (γ : SL(2, ℤ)) (hf : ∀ z, f (sm γ z) = f z) {τ : ℂ}
    (hτ : 0 < τ.im) {c : ℂ} (h : Tendsto f (𝓝[≠] (sm γ τ)) (𝓝 c)) : Tendsto f (𝓝[≠] τ) (𝓝 c) := by
  have := h.comp (tendsto_sm_nhdsNE γ hτ)
  refine this.congr fun z => ?_
  simp only [Function.comp_apply, hf]

theorem V_sm (γ : Γ) (τ : ℍ) : D.V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = D.V τ := by
  rw [← sm_coe]
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have hinv : ∀ z, D.Vraw (sm ((γ⁻¹ : Γ) : SL(2, ℤ)) z) = D.Vraw z := D.Vraw_sm γ⁻¹
  by_cases h : ∃ c, Tendsto D.Vraw (𝓝[≠] (τ : ℂ)) (𝓝 c)
  · obtain ⟨c, hc⟩ := h
    have h1 : Tendsto D.Vraw (𝓝[≠] (sm (γ : SL(2, ℤ)) τ)) (𝓝 c) := by
      refine tendsto_of_tendsto_sm ((γ⁻¹ : Γ) : SL(2, ℤ)) hinv (im_sm_pos _ _) ?_
      rw [Subgroup.coe_inv, sm_inv_sm _ hτ]; exact hc
    simp only [V]
    rw [regularize_eq_of_tendsto h1, regularize_eq_of_tendsto hc]
  · have h' : ¬ ∃ c, Tendsto D.Vraw (𝓝[≠] (sm (γ : SL(2, ℤ)) τ)) (𝓝 c) := by
      rintro ⟨c, hc⟩
      exact h ⟨c, tendsto_of_tendsto_sm (γ : SL(2, ℤ)) (D.Vraw_sm γ) hτ hc⟩
    simp only [V]
    rw [regularize_eq_zero h, regularize_eq_zero h']

theorem exists_height : ∃ Y : ℝ, ∀ z : ℂ, 0 < z.im → Y < z.im →
    ∀ s ∈ D.S, ∀ γ : SL(2, ℤ), sm γ z ∉ D.Kk s := by
  have key : ∀ s, s ∈ D.S → ∃ Y : ℝ, 0 ≤ Y ∧ ∀ z : ℂ, 0 < z.im → Y < z.im →
      ∀ γ : SL(2, ℤ), sm γ z ∉ D.Kk s := by
    intro s hs
    obtain ⟨ε, B, hε, hK⟩ := D.heights hs
    refine ⟨max B ε⁻¹, le_max_of_le_right (inv_nonneg.2 hε.le), fun z hz hY γ hmem => ?_⟩
    exact absurd (im_le_of_sm_mem hε hK γ hz hmem) (not_le.2 hY)
  choose! Y hY0 hY using key
  refine ⟨∑ s ∈ D.S, Y s, fun z hz hlt s hs γ => hY s hs z hz ?_ γ⟩
  exact lt_of_le_of_lt (Finset.single_le_sum (fun t ht => hY0 t ht) hs) hlt

theorem Vraw_eq_one_of_high {Y : ℝ} (hY : ∀ z : ℂ, 0 < z.im → Y < z.im →
    ∀ s ∈ D.S, ∀ γ : SL(2, ℤ), sm γ z ∉ D.Kk s) (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im)
    (hzY : Y < z.im) : D.Vraw (sm σ z) = 1 := by
  simp only [Vraw]
  refine Finset.prod_eq_one fun s hs => finprod_eq_one_of_forall_eq_one fun δ => ?_
  simp only [fac]
  rw [← sm_mul, D.hd1 s hs _ (hY z hz hzY s hs _), one_zpow]

theorem V_cusp (σ : SL(2, ℤ)) : ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → D.V (sm σ z) = 1 := by
  obtain ⟨Y, hY⟩ := D.exists_height
  refine ⟨max Y 0, fun z hz => ?_⟩
  have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  have hzY : Y < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  apply regularize_eq_of_tendsto
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  have hw : 0 < (sm σ z).im := im_sm_pos σ z

  have hev : D.Vraw =ᶠ[𝓝 (sm σ z)] fun _ => 1 := by
    have hU : ∀ᶠ w in 𝓝 (sm σ z), 0 < w.im :=
      (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hw
    have hc : ContinuousAt (fun w => (sm σ⁻¹ w).im) (sm σ z) :=
      Complex.continuous_im.continuousAt.comp (continuousAt_sm σ⁻¹ hw)
    have hY' : ∀ᶠ w in 𝓝 (sm σ z), Y < (sm σ⁻¹ w).im := by
      refine hc.eventually (p := fun t => Y < t) (isOpen_Ioi.mem_nhds ?_)
      show Y < (sm σ⁻¹ (sm σ z)).im
      rw [sm_inv_sm σ hz0]; exact hzY
    filter_upwards [hU, hY'] with w hw1 hw2
    have : w = sm σ (sm σ⁻¹ w) := by
      conv_lhs => rw [← sm_inv_sm σ⁻¹ hw1]
      rw [inv_inv]
    rw [this]
    exact D.Vraw_eq_one_of_high hY σ (im_sm_pos _ _) hw2
  exact (tendsto_const_nhds.congr' hev.symm)

end Data
end
end Dubon2026.SourceSmoothDivisor
