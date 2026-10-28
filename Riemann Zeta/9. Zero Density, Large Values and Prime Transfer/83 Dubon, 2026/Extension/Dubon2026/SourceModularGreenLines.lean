import Dubon2026.SourceModularGreenDomain
/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> winding-period identity
-> Green's formula on the actual modular fundamental domain.
Adapted from pinned Apache-2.0 anthropics/fermats-last-theorem source.
Native Fubini, one-dimensional FTC and real change-of-variable theorems provide
the shorter rigorous route for the curved boundary; no boundary identity is
assumed. No incidental open-neighborhood assumption is retained. -/
namespace Dubon2026.SourceModularGreen
noncomputable section
open Complex MeasureTheory Set Filter Topology

variable (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hDU : D ⊆ U) (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
  (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
  (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im))

lemma mk_eq (x y : ℝ) : (⟨x, y⟩ : ℂ) = (x : ℂ) + (y : ℂ) * I := Complex.mk_eq_add_mul_I x y

lemma hasDerivAt_vert {x y : ℝ} (hz : (⟨x, y⟩ : ℂ) ∈ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) :
    HasDerivAt (fun t : ℝ => Φ ⟨x, t⟩) (Φ' ⟨x, y⟩ I) y := by
  have h1 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)
  have h2 : (fun t : ℝ => Φ ⟨x, t⟩) = Φ ∘ fun t : ℝ => (x : ℂ) + (t : ℂ) * I := by
    ext t; simp [mk_eq]
  rw [h2]
  have hz' : (x : ℂ) + (y : ℂ) * I ∈ U := by rwa [← mk_eq]
  have := (hd _ hz').comp_hasDerivAt y h1
  rwa [← mk_eq] at this

lemma hasDerivAt_horiz {x y : ℝ} (hz : (⟨x, y⟩ : ℂ) ∈ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) :
    HasDerivAt (fun t : ℝ => Φ ⟨t, y⟩) (Φ' ⟨x, y⟩ 1) x := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I)
  have h2 : (fun t : ℝ => Φ ⟨t, y⟩) = Φ ∘ fun t : ℝ => (t : ℂ) + (y : ℂ) * I := by
    ext t; simp [mk_eq]
  rw [h2]
  have hz' : (x : ℂ) + (y : ℂ) * I ∈ U := by rwa [← mk_eq]
  have := (hd _ hz').comp_hasDerivAt x h1
  rwa [← mk_eq] at this

lemma continuous_mk_left (x : ℝ) : Continuous fun t : ℝ => (⟨x, t⟩ : ℂ) := by
  simp [mk_eq]
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

lemma continuous_mk_right (y : ℝ) : Continuous fun t : ℝ => (⟨t, y⟩ : ℂ) := by
  simp [mk_eq]
  exact (Complex.continuous_ofReal.add continuous_const)

lemma tendsto_const_mul_exp {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    Tendsto (fun t : ℝ => C * Real.exp (-δ * t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.exp (-δ * t)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_comp_nhds_zero.mpr ?_
    exact (tendsto_id (α := ℝ) (x := atTop)).const_mul_atTop_of_neg (neg_lt_zero.mpr hδ)
  simpa using h1.const_mul C

include hδ hDU hd hc hΦ hΦ' in

lemma integral_vert {x : ℝ} (hx : |x| ≤ 1 / 2) :
    ∫ y in Ioi (h x), Φ' ⟨x, y⟩ I = -Φ ⟨x, h x⟩ := by
  obtain ⟨C, hC⟩ := hΦ
  obtain ⟨C', hC'⟩ := hΦ'
  have hmem : ∀ t ∈ Ici (h x), (⟨x, t⟩ : ℂ) ∈ U := fun t ht => hDU (mk_mem_D hx ht)
  have hderiv : ∀ t ∈ Ici (h x), HasDerivAt (fun t : ℝ => Φ ⟨x, t⟩) (Φ' ⟨x, t⟩ I) t :=
    fun t ht => hasDerivAt_vert Φ Φ' U (hmem t ht) hd
  have hcont : ContinuousOn (fun t : ℝ => Φ' ⟨x, t⟩ I) (Ici (h x)) := by
    have h1 : ContinuousOn (fun t : ℝ => Φ' ⟨x, t⟩) (Ici (h x)) :=
      hc.comp (continuous_mk_left x).continuousOn hmem
    exact h1.clm_apply continuousOn_const
  have hint : IntegrableOn (fun t : ℝ => Φ' ⟨x, t⟩ I) (Ioi (h x)) := by
    have hdom : IntegrableOn (fun t : ℝ => C' * Real.exp (-δ * t)) (Ioi (h x)) :=
      (exp_neg_integrableOn_Ioi _ hδ).const_mul C'
    refine Integrable.mono' hdom
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    calc ‖Φ' ⟨x, t⟩ I‖ ≤ ‖Φ' ⟨x, t⟩‖ * ‖I‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Φ' ⟨x, t⟩‖ := by rw [Complex.norm_I, mul_one]
      _ ≤ C' * Real.exp (-δ * t) := hC' _ (hmem t (mem_Ici.mpr (le_of_lt ht)))
  have hlim : Tendsto (fun t : ℝ => Φ ⟨x, t⟩) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp hδ C)
    filter_upwards [Ici_mem_atTop (h x)] with t ht
    exact hC _ (hmem t ht)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim, zero_sub]

include hd in

lemma integral_horiz {a b y : ℝ} (hab : a ≤ b) (hmem : ∀ t ∈ Icc a b, (⟨t, y⟩ : ℂ) ∈ U)
    (hc : ContinuousOn Φ' U) :
    ∫ t in a..b, Φ' ⟨t, y⟩ 1 = Φ ⟨b, y⟩ - Φ ⟨a, y⟩ := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => Φ ⟨t, y⟩) (Φ' ⟨t, y⟩ 1) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_horiz Φ Φ' U (hmem t ht) hd
  have hcont : ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩ 1) (uIcc a b) := by
    rw [uIcc_of_le hab]
    have h1 : ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩) (Icc a b) :=
      hc.comp (continuous_mk_right y).continuousOn hmem
    exact h1.clm_apply continuousOn_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)


end
end Dubon2026.SourceModularGreen
