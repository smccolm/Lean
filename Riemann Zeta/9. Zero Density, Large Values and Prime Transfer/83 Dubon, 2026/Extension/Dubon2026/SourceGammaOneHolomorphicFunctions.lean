import Dubon2026.SourceGammaOneAnalyticResidues
import Dubon2026.SourceHolomorphicQuotientExtension

/-! DUB-17/18 -> original Gamma1 Picard-period comparison -> finite-place
exhaustion. Regularity at all actual analytic places gives a holomorphic
realization of the original modular quotient. Its exact quotient identity
derives subgroup invariance; no analytic representative is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold MatrixGroups ModularForm
variable {Γ : Subgroup SL(2, ℤ)}

theorem holomorphic_quotient_invariant {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (F : ℍ → ℂ) (hF : MDiff F) (hFg : ∀ τ, F τ * h τ = g τ) :
    ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ := by
  intro γ hγ
  have heq : F ∣[(0 : ℤ)] γ = F := by
    refine HolomorphicQuotient.eq_of_eq_off_zeros
      (fun c hc => ModularRatios.eventually_ne_zero_ofComplex h hh ⟨c, hc⟩)
      (hF.slash 0 (γ : GL (Fin 2) ℝ)).continuous hF.continuous (fun τ hτ => ?_)
    rw [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
    have eh := SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
    have eg := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
    have hd := zpow_ne_zero k (denom_ne_zero γ τ)
    have e1 := hFg (γ • τ)
    have e2 := hFg τ
    rw [eh, eg] at e1
    have he : F (γ • τ) * (denom γ τ ^ k * h τ) =
        F τ * (denom γ τ ^ k * h τ) := by
      rw [e1, ← e2]
      ring
    exact mul_right_cancel₀ (mul_ne_zero hd hτ) he
  intro τ
  have he := congrFun heq τ
  simpa only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one] using he

theorem holomorphic_realization_of_mem_all_analytic_places
    (hT : ModularGroup.T ∈ Γ) (x : functionFieldOver Γ ℂ)
    (hx : ∀ τ : ℍ, x ∈ (analyticPlace hT τ).toValuationSubring) :
    ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (F : ℍ → ℂ),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g ∧
      MDiff F ∧ (∀ τ, F τ * h τ = g τ) ∧
      ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ := by
  obtain ⟨k, g, h, hh, hr⟩ := functionFieldOver_modular_ratio hT x
  obtain ⟨F, hF, he⟩ := HolomorphicQuotient.exists_mdifferentiable_mul_eq
    g.holo' h.holo'
    (fun c hc => ModularRatios.eventually_ne_zero_ofComplex h hh ⟨c, hc⟩) (by
      intro τ
      have hord := (analyticPlace_mem_iff hT τ x).mp (hx τ)
      obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg
        (meromorphicAt_realize hT x τ)).mpr hord
      refine ⟨‖c‖ + 1, ?_⟩
      have hb := hc.norm.eventually (eventually_le_nhds (by linarith : ‖c‖ < ‖c‖ + 1))
      filter_upwards [hb, realize_eventuallyEq_of_ratio hT g h x hh hr τ] with z hz heq
      rwa [heq] at hz)
  exact ⟨k, g, h, F, hh, hr, hF, he, holomorphic_quotient_invariant g h hh F hF he⟩

end
end Dubon2026.SourceFunctionField.GammaOne
