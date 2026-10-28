import Dubon2026.SourceMeromorphicMultiplierParabolic
import Dubon2026.SourceGammaOneRealPeriodSurjectivity
import Dubon2026.SourceWeightTwoPeriodUntwist

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
construction of the prescribed meromorphic function. Normalize any actual
meromorphic multiplier by exp(-Ek) using the existing real-period
surjectivity applied to log of its norm. This discharges unit modulus while
preserving every original meromorphic order and nonzero cusp limit.
Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice.lean
(Apache-2.0; retained LICENSE and NOTICE). -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter CongruenceSubgroup Matrix.SpecialLinearGroup
open SourceMeromorphicMultiplier SourcePeriodUntwist
open scoped MatrixGroups Topology

theorem exists_unitary_multiplier_same_orders (N : ℕ) [NeZero N]
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ (F₁ : ℍ → ℂ) (χ₁ : Gamma1 N → ℂ),
      (∀ τ : ℍ, MeromorphicAt (F₁ ∘ ofComplex) (τ : ℂ)) ∧
      (∀ (γ : Gamma1 N) (τ : ℍ), F₁ (γ.val • τ) = χ₁ γ * F₁ τ) ∧
      (∀ γ, ‖χ₁ γ‖ = 1) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Tendsto (fun τ : ℍ => F₁ (σ • τ)) atImInfty (𝓝 L)) ∧
      ∀ τ : ℍ, meromorphicOrderAt (F₁ ∘ ofComplex) (τ : ℂ) =
        meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) := by
  classical
  obtain ⟨τ₀, hτ₀⟩ := exists_apply_ne_zero hcusp
  have hone : χ 1 = 1 := multiplier_one hχ hτ₀
  have hmul : ∀ γ δ : Gamma1 N, χ (γ * δ) = χ γ * χ δ :=
    multiplier_mul hχ hτ₀
  have hne (γ : Gamma1 N) : χ γ ≠ 0 := by
    have he : χ γ * χ γ⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    intro hzero
    rw [hzero, zero_mul] at he
    exact zero_ne_one he
  let φ : Additive (Gamma1 N) →+ ℝ :=
    { toFun := fun x => Real.log ‖χ x.toMul‖
      map_zero' := by
        change Real.log ‖χ 1‖ = 0
        rw [hone, norm_one, Real.log_one]
      map_add' := fun x y => by
        change Real.log ‖χ (x.toMul * y.toMul)‖ = _
        rw [hmul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hne _))
          (norm_ne_zero_iff.mpr (hne _))] }
  have hφ (γ : Gamma1 N) : φ (Additive.ofMul γ) = Real.log ‖χ γ‖ := rfl
  have hp : ∀ γ : Gamma1 N, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0 := by
    intro γ hγ
    rw [hφ, multiplier_eq_one_of_trace_sq hχ hcusp γ hγ, norm_one, Real.log_one]
  obtain ⟨k, hk⟩ := sourceGamma1_exists_cuspForm_of_real_parabolic_character N φ hp
  let F₁ : ℍ → ℂ := fun τ => F τ * Complex.exp (-Ek k τ)
  let χ₁ : Gamma1 N → ℂ := fun γ => χ γ * Complex.exp (-sourceWeightTwoPeriodValue (Gamma1 N) k γ)
  have hG (τ : ℍ) : AnalyticAt ℂ (fun z => Complex.exp (-Ek k z)) (τ : ℂ) :=
    (analyticAt_Ek k τ.im_pos).neg.cexp'
  have hprod : F₁ ∘ ofComplex = (F ∘ ofComplex) * (fun z => Complex.exp (-Ek k z)) := by
    funext z
    simp only [F₁, Function.comp_apply, Pi.mul_apply, Ek, ofComplex_apply]
  refine ⟨F₁, χ₁, fun τ => ?_, fun γ τ => ?_, fun γ => ?_, fun σ => ?_, fun τ => ?_⟩
  · rw [hprod]
    exact (hF τ).mul (hG τ).meromorphicAt
  · dsimp only [F₁, χ₁]
    rw [hχ γ τ, Ek_smul k γ τ, neg_add, Complex.exp_add]
    ring
  · dsimp only [χ₁]
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hk γ, hφ, Real.exp_neg,
      Real.exp_log (norm_pos_iff.mpr (hne γ)), mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne γ))]
  · obtain ⟨L, hL0, hL⟩ := hcusp σ
    obtain ⟨L', hL'⟩ := Ek_exists_cusp_limit k σ
    exact ⟨L * Complex.exp (-L'), mul_ne_zero hL0 (Complex.exp_ne_zero _), hL.mul hL'.neg.cexp⟩
  · have h0 : analyticOrderAt (fun z => Complex.exp (-Ek k z)) (τ : ℂ) = 0 :=
      (hG τ).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
    rw [hprod, meromorphicOrderAt_mul (hF τ) (hG τ).meromorphicAt,
      (hG τ).meromorphicOrderAt_eq, h0, ENat.map_zero, Nat.cast_zero, WithTop.coe_zero, add_zero]

end
end Dubon2026.SourceFunctionField.GammaOne
