import Dubon2026.SourceMeromorphicTranslatedGerms

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> cusp behavior of the invariant untwist.
Transfer bounds through native punctured upper-half-plane neighborhoods.
The original nonzero cusp limit is retained, rather than replaced by a
boundedness premise or a new limit assumption for the normalized function. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem near_cusp_translated (F : ℍ → ℂ) (σ : SL(2, ℤ)) {L : ℂ}
    (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℍ, A < τ.im →
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), dist (F (σ • ofComplex z)) L < ε := by
  obtain ⟨B, hB⟩ := (UpperHalfPlane.atImInfty_mem _).mp (Metric.tendsto_nhds.mp hL ε hε)
  refine ⟨max B 0, le_max_right _ _, fun τ hτ => ?_⟩
  have hτB : B < τ.im := lt_of_le_of_lt (le_max_left _ _) hτ
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτB),
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz hz0
  simpa only [ofComplex_apply_of_im_pos hz0] using hB (⟨z, hz0⟩ : ℍ) hz.le

theorem reg_near_cusp (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℍ, A < τ.im →
      meromorphicOrderAt (F ∘ ofComplex) ((σ • τ : ℍ) : ℂ) = 0 ∧
        dist (reg F ((σ • τ : ℍ) : ℂ)) L ≤ ε := by
  obtain ⟨A₁, hA₁, h₁⟩ := near_cusp_translated F σ hL (half_pos (norm_pos_iff.mpr hL0))
  obtain ⟨B, hB⟩ := (UpperHalfPlane.atImInfty_mem _).mp (Metric.tendsto_nhds.mp hL ε hε)
  refine ⟨max A₁ B, le_trans hA₁ (le_max_left _ _), fun τ hτ => ?_⟩
  have hτ₁ : A₁ < τ.im := lt_of_le_of_lt (le_max_left _ _) hτ
  have hτB : B < τ.im := lt_of_le_of_lt (le_max_right _ _) hτ
  have ho : meromorphicOrderAt (F ∘ ofComplex) ((σ • τ : ℍ) : ℂ) = 0 := by
    rw [← order_translate F σ τ]
    exact meromorphicOrderAt_eq_zero_of_near (meromorphicAt_translate F hF σ τ)
      hL0 (h₁ τ hτ₁)
  refine ⟨ho, ?_⟩
  have hcσ : ContinuousAt (fun w : ℍ => ((σ • w : ℍ) : ℂ)) τ :=
    continuous_coe.continuousAt.comp
      ((Homeomorph.smul (σ : GL (Fin 2) ℝ)).continuous.continuousAt (x := τ))
  have hc : ContinuousAt (fun w : ℍ => reg F ((σ • w : ℍ) : ℂ)) τ :=
    ContinuousAt.comp (f := fun w : ℍ => ((σ • w : ℍ) : ℂ)) (x := τ)
      (analyticAt_reg_of_order_zero F hF (σ • τ) ho).continuousAt hcσ
  have ht : Tendsto (fun w : ℍ => σ • w) (𝓝[≠] τ) (𝓝[≠] (σ • τ)) :=
    le_of_eq ((Homeomorph.smul (σ : GL (Fin 2) ℝ)).map_punctured_nhds_eq τ)
  have he := (reg_eq_nhdsNE F hF (σ • τ)).comp_tendsto ht
  apply le_of_tendsto ((hc.tendsto.mono_left
    (show 𝓝[≠] τ ≤ 𝓝 τ from nhdsWithin_le_nhds)).dist tendsto_const_nhds)
  filter_upwards [he, eventually_nhdsWithin_of_eventually_nhds
    (continuous_im.continuousAt.tendsto.eventually (Ioi_mem_nhds hτB))] with w hw hwB
  change reg F ((σ • w : ℍ) : ℂ) = F (σ • w) at hw
  rw [hw]
  exact (hB w hwB.le).le

theorem tendsto_reg_cusp (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    Tendsto (fun τ : ℍ => reg F ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A, -, hA⟩ := reg_near_cusp F hF σ hL0 hL (half_pos hε)
  apply (UpperHalfPlane.atImInfty_mem _).mpr
  refine ⟨A + 1, fun τ hτ => ?_⟩
  have hb := (hA τ (by linarith)).2
  change dist (reg F ((σ • τ : ℍ) : ℂ)) L < ε
  linarith

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem Φ_cusp (F : ℍ → ℂ) (k : CuspForm (Γ.map (mapGL ℝ)) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ F k ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c) := by
  obtain ⟨L₂, hL₂⟩ := Ek_exists_cusp_limit k σ
  refine ⟨L * Complex.exp (-(2 * Real.pi * Complex.I) * ((L₂.re : ℂ))),
    mul_ne_zero hL0 (Complex.exp_ne_zero _), ?_⟩
  have hg : Continuous fun x : ℂ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * ((x.re : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp Complex.continuous_re))
  exact (tendsto_reg_cusp F hF σ hL0 hL).mul ((hg.tendsto L₂).comp hL₂)

end
end Dubon2026.SourcePeriodUntwist
