import Dubon2026.SourceLevelOneAnalyticJPolynomial

/-! DUB-17/18 -> original all-weight arithmetic association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> cusp differential
realization -> rational Fourier structure -> invariant Fricke fractions.
Clear the actual finite cusp pole by a discriminant power and apply the
existing level-one reduction through its proved analytic realization. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SourceFunctionField
open scoped MatrixGroups ModularForm Manifold

/-- The actual weight-zero invariant after clearing its pole by Delta^m. -/
def poleClearedLevelOne (m : ℕ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hbd : IsBoundedAtImInfty (f * (discriminant : ℍ → ℂ) ^ m)) :
    ModularForm 𝒮ℒ (12 * (m : ℤ)) := by
  let D : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
    ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow m).mcast (by ring)
  have hD : (D : ℍ → ℂ) = (discriminant : ℍ → ℂ) ^ m := by
    simp [D, ModularForm.coe_pow, CuspForm.coe_discriminant]
  have hslash : ∀ γ : SL(2, ℤ), (f * ⇑D) ∣[(12 * (m : ℤ))] γ = f * ⇑D := by
    intro γ
    have he := ModularForm.mul_slash_SL2 0 (12 * (m : ℤ)) γ f (D : ℍ → ℂ)
    rw [zero_add] at he
    have hDslash : (D : ℍ → ℂ) ∣[(12 * (m : ℤ))] γ = D :=
      SlashInvariantFormClass.slash_action_eq (Γ := 𝒮ℒ) (k := 12 * (m : ℤ)) D
        (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩
    rw [he, hinv γ, hDslash]
  exact {
    toFun := f * ⇑D
    slash_action_eq' := by
      rintro γ ⟨g, rfl⟩
      exact hslash g
    holo' := hf.mul D.holo'
    bdd_at_cusps' := by
      intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
      intro γ _
      rw [hslash, hD]
      exact hbd
  }

theorem poleClearedLevelOne_apply (m : ℕ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hbd : IsBoundedAtImInfty (f * (discriminant : ℍ → ℂ) ^ m)) (τ : ℍ) :
    poleClearedLevelOne m f hf hinv hbd τ = f τ * discriminant τ ^ m := by
  change f τ * ((((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow m).mcast
    (show (m : ℤ) * 12 = 12 * (m : ℤ) by ring)) : ModularForm 𝒮ℒ _) τ = _
  rw [ModularForm.coe_mcast, ModularForm.coe_pow]
  rfl

theorem exists_polynomial_j_of_poleBounded_invariant (m : ℕ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hinv : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hbd : IsBoundedAtImInfty (f * (discriminant : ℍ → ℂ) ^ m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ f = fun τ => P.eval (JMultiplicity.jf τ) := by
  obtain ⟨P, hdeg, hP⟩ := exists_levelOne_analytic_j_polynomial m
    (poleClearedLevelOne m f hf hinv hbd)
  refine ⟨P, hdeg, funext fun τ => ?_⟩
  have he := hP τ
  rw [poleClearedLevelOne_apply] at he
  exact mul_right_cancel₀ (pow_ne_zero _ (discriminant_ne_zero τ)) he

end
end Dubon2026.SourceFricke
