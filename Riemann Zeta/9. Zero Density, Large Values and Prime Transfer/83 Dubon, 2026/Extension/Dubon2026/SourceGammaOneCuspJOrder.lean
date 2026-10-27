import Dubon2026.SourceGammaOneCuspOrder
import Dubon2026.SourceGammaOneJRealization
import Dubon2026.SourceCuspWeightFactors
import Dubon2026.SourceMeromorphicCuspPoleClearing

/-! DUB-17/18 -> actual Gamma1 regular-differential/cusp converse ->
nontrivial cusp places. The actual j coordinate is invariant under every
SL2 translate. Its cusp expression E4^3/Delta has negative order: E4 tends
to one and Delta has a positive finite order. This avoids a cusp-width
classification or a numerical field-degree bound. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter ModularForm
open scoped MatrixGroups ModularForm Topology Manifold
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

theorem analyticAt_levelOne_cuspFunction (N : ℕ) [NeZero N] {k : ℤ}
    (f : ModularForm 𝒮ℒ k) : AnalyticAt ℂ (cuspFunction N f) 0 := by
  have hp : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) N := by
    simpa using (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL).nat_mul N
  exact UpperHalfPlane.analyticAt_cuspFunction_zero (by exact_mod_cast NeZero.pos N)
    hp f.holo' (ModularFormClass.bdd_at_infty f)

theorem cusp_order_zero_of_tendsto_one (N : ℕ) [NeZero N] {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hf : Tendsto (f : ℍ → ℂ) atImInfty (𝓝 1)) :
    meromorphicOrderAt (cuspFunction N f) 0 = 0 := by
  have ha := analyticAt_levelOne_cuspFunction N f
  have hp : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) N := by
    simpa using (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL).nat_mul N
  have hv : cuspFunction N f 0 = 1 :=
    (UpperHalfPlane.cuspFunction_apply_zero (by exact_mod_cast NeZero.pos N) ha hp).trans hf.limUnder_eq
  apply (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero ha.meromorphicAt).mp
  refine ⟨1, one_ne_zero, ?_⟩
  rw [← hv]
  exact ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem cuspOrder_jCoordinate (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Γ)
    (γ : SL(2, ℤ)) :
    cuspOrder Γ N γ (jCoordinateOver Γ ℂ) =
      -meromorphicOrderAt (cuspFunction N ModularForm.discriminant) 0 := by
  have he : cuspRealize Γ N γ (jCoordinateOver Γ ℂ : LaurentSeries ℂ) =
      cuspFunction N JMultiplicity.jf := by
    unfold cuspRealize
    congr 1
    funext τ
    rw [realize_jCoordinateOver hT, JMultiplicity.jf_smul]
  have hq : cuspFunction N JMultiplicity.jf =ᶠ[𝓝[≠] (0 : ℂ)]
      (cuspFunction N (E₄ : ℍ → ℂ)) ^ 3 / cuspFunction N ModularForm.discriminant := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
      Function.comp_apply, JMultiplicity.jf, Pi.div_apply, Pi.pow_apply]
  have h4 := (analyticAt_levelOne_cuspFunction N E₄).meromorphicAt
  have hd : MeromorphicAt (cuspFunction N ModularForm.discriminant) 0 := by
    simpa only [CuspForm.coe_discriminant] using
      (analyticAt_levelOne_cuspFunction N (CuspForm.discriminant : ModularForm 𝒮ℒ 12)).meromorphicAt
  unfold cuspOrder
  rw [he, meromorphicOrderAt_congr hq, meromorphicOrderAt_div (h4.pow 3) hd,
    meromorphicOrderAt_pow h4, cusp_order_zero_of_tendsto_one N E₄ JMultiplicity.tendsto_E₄_atImInfty]
  simp

theorem cuspOrder_jCoordinate_neg (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Γ)
    (γ : SL(2, ℤ)) : cuspOrder Γ N γ (jCoordinateOver Γ ℂ) < 0 := by
  have hd : MeromorphicAt (cuspFunction N ModularForm.discriminant) 0 := by
    simpa only [CuspForm.coe_discriminant] using
      (analyticAt_levelOne_cuspFunction N (CuspForm.discriminant : ModularForm 𝒮ℒ 12)).meromorphicAt
  have ht : meromorphicOrderAt (cuspFunction N ModularForm.discriminant) 0 ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hd).mpr
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
      Function.comp_apply]
    exact ModularForm.discriminant_ne_zero _
  have hp : 0 < meromorphicOrderAt (cuspFunction N ModularForm.discriminant) 0 := by
    simpa only [CuspForm.coe_discriminant] using SourceFricke.meromorphicOrderAt_discriminant_cusp_pos N
  obtain ⟨d, hd'⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [cuspOrder_jCoordinate N hT γ, ← hd']
  rw [← hd', ← WithTop.coe_zero, WithTop.coe_lt_coe] at hp
  exact_mod_cast neg_neg_of_pos hp

theorem exists_cuspOrder_pos (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ) (γ : SL(2, ℤ)) :
    ∃ x : functionFieldOver Γ ℂ, 0 < cuspOrder Γ N γ x ∧ cuspOrder Γ N γ x ≠ ⊤ := by
  have hj0 : jCoordinateOver Γ ℂ ≠ 0 := by
    intro he
    exact transcendental_jCoordinateOver Γ ℂ (he ▸ isAlgebraic_zero)
  have hjt := cuspOrder_ne_top N hΓ hT γ hj0
  have hit := cuspOrder_ne_top N hΓ hT γ (inv_ne_zero hj0)
  have hneg := cuspOrder_jCoordinate_neg N hT γ
  refine ⟨(jCoordinateOver Γ ℂ)⁻¹, ?_, hit⟩
  have hs : cuspOrder Γ N γ (jCoordinateOver Γ ℂ)⁻¹ +
      cuspOrder Γ N γ (jCoordinateOver Γ ℂ) = 0 := by
    rw [← cuspOrder_mul N hΓ hT γ, inv_mul_cancel₀ hj0, cuspOrder_one N hT γ]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hjt
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hit
  rw [← ha, ← hb, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hs
  rw [← ha, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hneg
  rw [← hb, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  omega

end
end Dubon2026.SourceFunctionField.GammaOne
