import Dubon2026.SourceHolomorphicQuotientExtension

/-! DUB-17/18 -> finite-place exhaustion -> bounded original functions
integral over C[j]. The proved modular representation and actual
boundedness of the original realization supply every hypothesis of
removable-singularity extension. The resulting holomorphic function
has the exact numerator/denominator identity at every complex point.
Bounds at all cusps and a discriminant-power modular representation
remain to be proved before the integrality consumer applies.
The slash-invariance argument adapts anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold MatrixGroups ModularForm

theorem original_holomorphic_quotient_of_bounded (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ)
    (hb : ∀ τ : ℍ, IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
      (fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) z‖)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (F : ℍ → ℂ),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g ∧
        MDiff F ∧ ∀ τ, F τ * h τ = g τ := by
  obtain ⟨k, g, h, hh, hx⟩ := original_field_modular_ratio N x
  have he : ∃ F : ℍ → ℂ, MDiff F ∧ ∀ τ, F τ * h τ = g τ := by
    apply HolomorphicQuotient.exists_mdifferentiable_mul_eq
      (ModularFormClass.holo g) (ModularFormClass.holo h)
    · intro c hc
      exact ModularRatios.eventually_ne_zero_ofComplex h hh ⟨c, hc⟩
    · intro τ
      obtain ⟨M, hM⟩ := isBoundedUnder_nhdsNE_coe_iff.mpr (hb τ)
      refine ⟨M, ?_⟩
      filter_upwards [hM, realize_eventuallyEq_of_ratio g h x hh hx τ] with z hz heq
      change ‖realize N (x : LaurentSeries ℂ) (ofComplex z)‖ ≤ M at hz
      rwa [heq] at hz
  obtain ⟨F, hF, hFg⟩ := he
  exact ⟨k, g, h, F, hh, hx, hF, hFg⟩

theorem holomorphic_quotient_slash_zero {N : ℕ} {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (F : ℍ → ℂ) (hF : MDiff F) (hFg : ∀ τ, F τ * h τ = g τ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    F ∣[(0 : ℤ)] γ = F := by
  refine HolomorphicQuotient.eq_of_eq_off_zeros
    (fun c hc => ModularRatios.eventually_ne_zero_ofComplex h hh ⟨c, hc⟩)
    (hF.slash 0 (γ : GL (Fin 2) ℝ)).continuous hF.continuous (fun τ hτ => ?_)
  rw [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  have eh : h (γ • τ) = denom γ τ ^ k * h τ := SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
  have eg : g (γ • τ) = denom γ τ ^ k * g τ := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  have hd : (denom γ τ) ^ k ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
  have e1 := hFg (γ • τ)
  have e2 := hFg τ
  rw [eh, eg] at e1
  have he : F (γ • τ) * (denom γ τ ^ k * h τ) = F τ * (denom γ τ ^ k * h τ) := by
    rw [e1, ← e2]
    ring
  exact mul_right_cancel₀ (mul_ne_zero hd hτ) he

end
end Dubon2026.SourceFunctionField
