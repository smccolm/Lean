import Dubon2026.SourceInverseJLimits

/-! Surjectivity of the existing analytic j-coordinate. A missing value would
give a holomorphic modular form of weight -12 by inverting E4^3-c Delta;
Mathlib's negative-weight vanishing rules this out. This allows every complex
elliptic curve to be compared with an actual period curve for the odd-prime
product identity, required by DUB-17/18 through cyclic roots and inertia.
Adapted from the mathematical argument in anthropics/fermats-last-theorem,
Apache-2.0, 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_jLattice_surjective.lean. -/

namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane Filter ModularForm Complex SlashInvariantForm
open scoped Topology ModularForm Manifold MatrixGroups Modular

/-- The actual weight-twelve pencil whose zero gives a prescribed j-value. -/
def jPencil (c : ℂ) (τ : ℍ) : ℂ := E₄ τ ^ 3 - c * discriminant τ

theorem jPencil_smul (c : ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    jPencil c (γ • τ) = denom γ τ ^ (12 : ℤ) * jPencil c τ := by
  simp only [jPencil, E₄_smul, Δ_smul, mul_pow]
  have h : (denom γ τ ^ (4 : ℤ)) ^ 3 = denom γ τ ^ (12 : ℤ) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  rw [h]
  ring

theorem tendsto_jPencil_atImInfty (c : ℂ) :
    Tendsto (jPencil c) atImInfty (𝓝 1) := by
  simpa only [jPencil, one_pow, mul_zero, sub_zero] using
    (tendsto_E₄_atImInfty.pow 3).sub (tendsto_discriminant_atImInfty.const_mul c)

theorem inv_jPencil_slash (c : ℂ) (γ : SL(2, ℤ)) :
    (fun τ => (jPencil c τ)⁻¹) ∣[(-12 : ℤ)] γ =
      fun τ => (jPencil c τ)⁻¹ := by
  ext τ
  rw [SL_slash_apply, neg_neg, jPencil_smul]
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ _
  field_simp

/-- Under the explicitly temporary nonvanishing assumption, the inverse
pencil is a genuine negative-weight modular form. -/
def inverseJPencil (c : ℂ) (hn : ∀ τ, jPencil c τ ≠ 0) : ModularForm 𝒮ℒ (-12) where
  toFun := fun τ => (jPencil c τ)⁻¹
  slash_action_eq' := by
    rintro γ ⟨g, rfl⟩
    exact inv_jPencil_slash c g
  holo' := ((mdiff_E₄.pow 3).sub (mdifferentiable_const.mul mdiff_Δ)).inv hn
  bdd_at_cusps' {p} hp := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hp
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hp]
    intro γ _
    rw [inv_jPencil_slash]
    have ht := (tendsto_jPencil_atImInfty c).inv₀ one_ne_zero
    exact ht.isBigO_one ℝ

theorem jPencil_has_zero (c : ℂ) : ∃ τ, jPencil c τ = 0 := by
  by_contra hn
  have hn' : ∀ τ, jPencil c τ ≠ 0 := not_exists.mp hn
  have h := ModularFormClass.levelOne_neg_weight_eq_zero
    (k := (-12 : ℤ)) (by norm_num) (inverseJPencil c hn')
  have hI : (jPencil c UpperHalfPlane.I)⁻¹ = 0 := congrFun h UpperHalfPlane.I
  exact hn' UpperHalfPlane.I (inv_eq_zero.mp hI)

theorem jf_surjective : Function.Surjective jf := by
  intro c
  obtain ⟨τ, hτ⟩ := jPencil_has_zero c
  refine ⟨τ, ?_⟩
  rw [jf, div_eq_iff (discriminant_ne_zero τ)]
  exact sub_eq_zero.mp hτ

end
end Dubon2026.SourceFunctionField.JMultiplicity
