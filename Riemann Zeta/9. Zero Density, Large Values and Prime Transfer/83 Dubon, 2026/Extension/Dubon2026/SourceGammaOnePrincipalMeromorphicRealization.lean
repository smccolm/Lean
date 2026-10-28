import Dubon2026.SourceGammaOneCuspResidues
import Dubon2026.SourceGammaOneAnalyticJOrders
import Dubon2026.SourceCurvePicardGroup

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> forward Abel-Jacobi implication.
Use an actual equal-weight modular quotient representing the principal field
element. Its modular laws give exact invariance even at zero denominators;
the existing cusp-order theorem gives nonzero limits at every cusp.
This avoids a new pointwise invariance framework for the chosen realization. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve Filter
open scoped MatrixGroups Topology ModularForm
variable {Γ : Subgroup SL(2, ℤ)}

theorem modular_ratio_smul {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) / h (γ • τ) =
      ModularForm.translate g (γ : GL (Fin 2) ℝ) τ /
        ModularForm.translate h (γ : GL (Fin 2) ℝ) τ := by
  change g (γ • τ) / h (γ • τ) =
    ((g : ℍ → ℂ) ∣[k] γ) τ / ((h : ℍ → ℂ) ∣[k] γ) τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply,
    mul_div_mul_right _ _ (zpow_ne_zero _ (denom_ne_zero γ τ))]

theorem modular_ratio_cusp_limit_of_order_zero (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (x : functionFieldOver Γ ℂ) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (γ : SL(2, ℤ)) (ho : cuspOrder Γ N γ x = 0) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => g (γ • τ) / h (γ • τ)) atImInfty (𝓝 L) := by
  obtain ⟨L, hL, hlim⟩ := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (meromorphicAt_cuspRealize N hΓ hT x γ)).mpr ho
  refine ⟨L, hL, ?_⟩
  let gt := ModularForm.translate g (γ : GL (Fin 2) ℝ)
  let ht := ModularForm.translate h (γ : GL (Fin 2) ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hpg : Function.Periodic ((gt : ℍ → ℂ) ∘ ofComplex) N :=
    SlashInvariantFormClass.periodic_comp_ofComplex gt
      (CuspAuxiliary.natCast_mem_strictPeriods_conj N hΓ γ)
  have hph : Function.Periodic ((ht : ℍ → ℂ) ∘ ofComplex) N :=
    SlashInvariantFormClass.periodic_comp_ofComplex ht
      (CuspAuxiliary.natCast_mem_strictPeriods_conj N hΓ γ)
  have hq := (Function.Periodic.qParam_tendsto hN).comp tendsto_coe_atImInfty
  have hl := (hlim.congr' (cuspRealize_eventuallyEq_of_ratio N hΓ hT g h x hh hr γ)).comp hq
  refine hl.congr' (Filter.Eventually.of_forall fun τ => ?_)
  dsimp only [Function.comp_apply, Pi.div_apply]
  rw [eq_cuspFunction τ hN.ne' hpg, eq_cuspFunction τ hN.ne' hph]
  exact (modular_ratio_smul g h γ τ).symm

theorem exists_invariant_meromorphic_of_principal (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (c : ℍ →₀ ℤ) (hc : Divisor.IsPrincipal (Finsupp.mapDomain (analyticPlace hT) c)) :
    ∃ F : ℍ → ℂ,
      (∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) ∧
      (∀ (γ : Γ) (τ : ℍ), F (γ.val • τ) = F τ) ∧
      (∀ γ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Tendsto (fun τ : ℍ => F (γ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
        (((analyticRamification hT τ : ℤ) *
          (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ) := by
  obtain ⟨x, hx0, hx⟩ := hc
  obtain ⟨k, g, h, hh, hr⟩ := functionFieldOver_modular_ratio hT x
  refine ⟨fun τ => g τ / h τ, ?_, ?_, ?_, ?_⟩
  · intro τ
    exact (ModularRatios.analyticAt_comp_ofComplex g τ).meromorphicAt.div
      (ModularRatios.analyticAt_comp_ofComplex h τ).meromorphicAt
  · intro γ τ
    change g (γ.val • τ) / h (γ.val • τ) = g τ / h τ
    rw [SlashInvariantForm.slash_action_eqn_SL'' g γ.property,
      SlashInvariantForm.slash_action_eqn_SL'' h γ.property,
      mul_div_mul_left _ _ (zpow_ne_zero _ (denom_ne_zero γ.val τ))]
  · intro γ
    apply modular_ratio_cusp_limit_of_order_zero N hΓ hT g h x hh hr γ
    rw [cuspPlace_order N hΓ hT γ x hx0]
    have hzero : (cuspPlace N hΓ hT γ).ord x = 0 := by
      rw [← hx]
      apply Finsupp.mapDomain_notin_range
      rintro ⟨τ, hτ⟩
      have hj : jCoordinateOver Γ ℂ ∈ (analyticPlace hT τ).toValuationSubring := by
        have hz := add_mem ((analyticPlace hT τ).mem_of_ord_nonneg
          (analyticPlace_j_sub_pos hT τ).le)
          ((analyticPlace hT τ).algebraMap_mem' (JMultiplicity.jf τ))
        simpa only [sub_add_cancel] using hz
      have hn := (analyticPlace hT τ).mem_iff_ord_nonneg.mp hj
      rw [hτ] at hn
      exact (not_le_of_gt (cuspPlace_j_neg N hΓ hT γ)) hn
    simp only [hzero, mul_zero, WithTop.coe_zero]
  · intro τ
    have he := meromorphicOrderAt_congr (realize_eventuallyEq_of_ratio hT g h x hh hr τ)
    have ho := analyticPlace_order hT τ x hx0
    rw [← hx] at ho
    exact he.symm.trans ho

end
end Dubon2026.SourceFunctionField.GammaOne
