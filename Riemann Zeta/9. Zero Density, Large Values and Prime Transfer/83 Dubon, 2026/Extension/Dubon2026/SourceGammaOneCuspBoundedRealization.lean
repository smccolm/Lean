import Dubon2026.SourceGammaOneCuspResidues
import Dubon2026.SourceGammaOneQuotientCuspSeries

/-! DUB-17/18 -> actual Gamma1 Picard/period comparison -> exhaustion
of cusp places. The existing holomorphic quotient and actual cusp residue
limit give boundedness at every modular cusp. Native weight-zero constancy
then identifies an everywhere regular realization with an actual constant
in the original function field. No compactification is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups ModularForm Topology Manifold
variable {Γ : Subgroup SL(2, ℤ)}
  (N : ℕ) [NeZero N] (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
  (hT : ModularGroup.T ∈ Γ)

include hΓ hT

theorem holomorphic_quotient_cusp_eventuallyEq {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (x : functionFieldOver Γ ℂ)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (F : ℍ → ℂ) (he : ∀ τ, F τ * h τ = g τ) (γ : SL(2, ℤ)) :
    cuspRealize Γ N γ (x : LaurentSeries ℂ) =ᶠ[𝓝[≠] (0 : ℂ)]
      cuspFunction N (fun τ : ℍ => F (γ • τ)) := by
  have hprod (τ : ℍ) : F (γ • τ) * ModularForm.translate h (γ : GL (Fin 2) ℝ) τ =
      ModularForm.translate g (γ : GL (Fin 2) ℝ) τ := by
    change F (γ • τ) * ((h : ℍ → ℂ) ∣[k] γ) τ = ((g : ℍ → ℂ) ∣[k] γ) τ
    rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ← mul_assoc, he]
  filter_upwards [cuspRealize_eventuallyEq_of_ratio N hΓ hT g h x hh hr γ,
    eventually_ne_zero_translated_cuspFunction N hΓ h hh γ,
    self_mem_nhdsWithin] with q hq hden hq0
  rw [hq]
  simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
    Function.comp_apply, Pi.div_apply] at hden ⊢
  exact ((eq_div_iff hden).mpr (hprod _)).symm

variable [Γ.FiniteIndex]

theorem holomorphic_quotient_bounded_of_cusp_regular {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (x : functionFieldOver Γ ℂ)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (F : ℍ → ℂ) (hF : MDiff F) (he : ∀ τ, F τ * h τ = g τ)
    (γ : SL(2, ℤ)) (hx : x ∈ (cuspPlace N hΓ hT γ).toValuationSubring) :
    IsBoundedAtImInfty (fun τ : ℍ => F (γ • τ)) := by
  have hinv := holomorphic_quotient_invariant g h hh F hF he
  have hp : Function.Periodic ((fun τ : ℍ => F (γ • τ)) ∘ ofComplex) N := by
    apply SourceFricke.periodic_of_principal_invariant
    intro δ hδ τ
    have hconj : γ * δ * γ⁻¹ ∈ Γ :=
      hΓ ((CongruenceSubgroup.Gamma_normal N).conj_mem δ hδ γ)
    change F (γ • (δ • τ)) = F (γ • τ)
    calc
      _ = F ((γ * δ * γ⁻¹) • (γ • τ)) := by simp only [mul_smul, inv_smul_smul]
      _ = _ := hinv _ hconj _
  have hhN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlim := (cuspRealize_tendsto_residue N hΓ hT γ x hx).congr'
    (holomorphic_quotient_cusp_eventuallyEq N hΓ hT g h hh x hr F he γ)
  have ht := hlim.comp ((Function.Periodic.qParam_tendsto hhN).comp tendsto_coe_atImInfty)
  have ht' : Tendsto (fun τ : ℍ => F (γ • τ)) atImInfty
      (𝓝 (placeEval hT (cuspPlace N hΓ hT γ) x)) := by
    convert ht using 1
    funext τ
    exact (eq_cuspFunction τ hhN.ne' hp).symm
  exact ht'.isBigO_one ℝ

theorem constant_of_mem_all_analytic_and_cusp_places
    (x : functionFieldOver Γ ℂ)
    (ha : ∀ τ : ℍ, x ∈ (analyticPlace hT τ).toValuationSubring)
    (hc : ∀ γ : SL(2, ℤ), x ∈ (cuspPlace N hΓ hT γ).toValuationSubring) :
    x ∈ Set.range (algebraMap ℂ (functionFieldOver Γ ℂ)) := by
  obtain ⟨k, g, h, F, hh, hr, hF, he, hinv⟩ :=
    holomorphic_realization_of_mem_all_analytic_places hT x ha
  let f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0 :=
    { toFun := F
      slash_action_eq' := by
        intro A hA
        obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ Γ, (γ : GL (Fin 2) ℝ) = A := by
          simpa using hA
        rw [← ModularForm.SL_slash]
        funext τ
        rw [ModularForm.SL_slash_apply, hinv γ hγ, neg_zero, zpow_zero, mul_one]
      holo' := hF
      bdd_at_cusps' := fun {c} hcus => by
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hcus)]
        intro γ _
        have hb := holomorphic_quotient_bounded_of_cusp_regular N hΓ hT g h hh x hr F hF he γ (hc γ)
        have hs : F ∣[(0 : ℤ)] γ = fun τ : ℍ => F (γ • τ) := by
          funext τ
          rw [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
        rw [hs]
        exact hb }
  obtain ⟨c, hcF⟩ := ModularForm.eq_const_of_weight_zero f
  have hFc (τ : ℍ) : F τ = c := congrFun hcF τ
  have hrep : CuspTaylor.Represents (x : LaurentSeries ℂ) (cuspFunction 1 F) := by
    rw [show (x : LaurentSeries ℂ) = ModularRatios.qL g / ModularRatios.qL h from
      (eq_div_iff (ModularRatios.qL_ne_zero hT h hh)).mpr hr]
    exact quotient_cusp_represents one_pos (hper hT) g h hh F he
  have hconst : cuspFunction 1 F =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => c := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
      Function.comp_apply, hFc]
  refine ⟨c, Subtype.ext ?_⟩
  exact (hrep.eq_series ((CuspTaylor.represents_const c).congr hconst)).symm

end
end Dubon2026.SourceFunctionField.GammaOne
