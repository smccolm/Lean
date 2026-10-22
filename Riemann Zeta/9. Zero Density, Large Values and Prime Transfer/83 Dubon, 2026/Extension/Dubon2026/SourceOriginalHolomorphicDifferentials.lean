import Dubon2026.SourceOriginalAnalyticDifferentialRegularity
import Dubon2026.SourceHolomorphicQuotientExtension

/-! DUB-17/18 -> matching cusp-form lower dimension -> analytic regular
differentials. The original regularity theorem removes every finite analytic
singularity of x dj. The existing native removable-singularity quotient
extension then supplies an actual holomorphic weight-two function. Its cusp
decay remains to be proved before treating it as a cusp form.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential Filter
open scoped Topology Manifold MatrixGroups ModularForm

theorem mdifferentiable_raw_j_derivative :
    MDiff (fun τ : ℍ => deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) := by
  have he : (fun τ : ℍ => deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) =
      fun τ => (2 * Real.pi * Complex.I) * Derivative.normalizedDerivOfComplex JMultiplicity.jf τ := by
    funext τ
    simpa only [ofComplex_apply] using JMultiplicity.deriv_jf_eq (τ : ℂ) τ.im_pos
  rw [he]
  exact mdifferentiable_const.mul
    (Derivative.normalizedDerivOfComplex_mdifferentiable JMultiplicity.mdifferentiable_jf)

theorem raw_j_derivative_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    deriv (JMultiplicity.jf ∘ ofComplex) ((γ • τ : ℍ) : ℂ) =
      denom γ τ ^ (2 : ℤ) * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) := by
  rw [JMultiplicity.deriv_jf_eq _ (γ • τ).im_pos, JMultiplicity.deriv_jf_eq _ τ.im_pos,
    ofComplex_apply, ofComplex_apply,
    JMultiplicity.D_smul JMultiplicity.mdifferentiable_jf JMultiplicity.jf_smul]
  simp only [zpow_ofNat]
  ring

theorem exists_original_holomorphic_differential (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hratio : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g) :
    ∃ F : ℍ → ℂ, MDiff F ∧
      (∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma0 N, F ∣[(2 : ℤ)] (γ : SL(2, ℤ)) = F := by
  obtain ⟨F, hF, hFg⟩ := HolomorphicQuotient.exists_mdifferentiable_mul_eq
    (g.holo'.mul mdifferentiable_raw_j_derivative) h.holo'
    (fun c hc => ModularRatios.eventually_ne_zero_ofComplex h hh ⟨c, hc⟩) (by
      intro τ
      obtain ⟨M, hM⟩ := original_regular_analytic_differential_bounded N x hx hreg τ
      refine ⟨M, ?_⟩
      filter_upwards [hM, realize_eventuallyEq_of_ratio g h x hh hratio τ,
        mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz he hp
      change ‖g (ofComplex z) * deriv (JMultiplicity.jf ∘ ofComplex) (ofComplex z) / h (ofComplex z)‖ ≤ M
      rw [he] at hz
      have hzc : ((ofComplex z : ℍ) : ℂ) = z := by
        rw [ofComplex_apply_of_im_pos hp]
      simpa only [mul_div_right_comm, hzc] using hz)
  change ∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) at hFg
  refine ⟨F, hF, hFg, ?_⟩
  intro γ hγ
  apply HolomorphicQuotient.eq_of_eq_off_zeros
    (fun c hc => ModularRatios.eventually_ne_zero_ofComplex h hh ⟨c, hc⟩)
    (hF.slash 2 (γ : GL (Fin 2) ℝ)).continuous hF.continuous
  intro τ hτ
  have eh := SlashInvariantForm.slash_action_eqn_SL'' h hγ τ
  have eg := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  have hd := zpow_ne_zero k (denom_ne_zero γ τ)
  have eγ := hFg (γ • τ)
  rw [eh, eg, raw_j_derivative_smul] at eγ
  have hFt : F (γ • τ) = denom γ τ ^ (2 : ℤ) * F τ := by
    apply mul_right_cancel₀ hτ
    apply mul_left_cancel₀ hd
    linear_combination eγ - denom γ τ ^ k * denom γ τ ^ (2 : ℤ) * hFg τ
  change (F ∣[(2 : ℤ)] γ) τ = F τ
  rw [ModularForm.SL_slash_apply, hFt, mul_right_comm,
    ← zpow_add₀ (denom_ne_zero γ τ)]
  norm_num

theorem original_regular_differential_holomorphic_realization (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (F : ℍ → ℂ),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g ∧
      MDiff F ∧
      (∀ τ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ)) ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma0 N, F ∣[(2 : ℤ)] (γ : SL(2, ℤ)) = F := by
  obtain ⟨k, g, h, hh, hr⟩ := original_field_modular_ratio N x
  obtain ⟨F, hF, he, hs⟩ := exists_original_holomorphic_differential N x hx hreg g h hh hr
  exact ⟨k, g, h, F, hh, hr, hF, he, hs⟩

end
end Dubon2026.SourceFunctionField
