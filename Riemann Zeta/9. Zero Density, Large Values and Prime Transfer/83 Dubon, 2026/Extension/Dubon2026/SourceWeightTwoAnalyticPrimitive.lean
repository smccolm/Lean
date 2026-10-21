import Dubon2026.SourceEichlerTransformation

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity -> actual original cusp-form primitives.
The existing scalar Eichler series, its exact derivative and its exact
transformation law supply the primitive. The normalization is fixed so
its derivative is the original cusp form and its period is the original
convergent cusp integral.
-/
namespace Dubon2026
noncomputable section
open Complex UpperHalfPlane Matrix.SpecialLinearGroup OnePoint
open scoped Real ModularForm MatrixGroups Manifold

/-- The actual first Eichler primitive with its original derivative normalization. -/
def sourceWeightTwoPrimitive (h : ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (2 * π * Complex.I)⁻¹ * sourceEichlerIntegral h 1 f z

/-- The constructed primitive has derivative equal to the actual original cusp form. -/
theorem sourceWeightTwoPrimitive_hasDerivAt
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 2) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (τ : ℍ) :
    HasDerivAt (sourceWeightTwoPrimitive h f ∘ ofComplex) (f τ) (τ : ℂ) := by
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hhol := ModularFormClass.holo f
  have hb := ModularFormClass.bdd_at_infty f
  have he := (UpperHalfPlane.mdifferentiableAt_iff.mp
    (mdifferentiable_sourceEichlerIntegral hh hp hhol hb 1 τ)).hasDerivAt
  have hv := congrFun (normalizedDerivOfComplex_sourceEichlerIntegral_one hh hp hhol hb) τ
  rw [CuspFormClass.qExpansion_coeff_zero f hh hΓ, sub_zero] at hv
  exact (he.const_mul (2 * π * Complex.I)⁻¹).congr_deriv hv

/-- The actual primitive transforms by precisely the original convergent cusp
integral; no period function or normalization factor is assumed. -/
theorem sourceWeightTwoPrimitive_transform
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic]
    (f : CuspForm Γ 2) (f' : CuspForm Γ' 2)
    {h h' : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hh' : 0 < h') (hΓ' : h' ∈ Γ'.strictPeriods)
    (σ : SL(2, ℤ)) (hf' : ⇑f' = ⇑f ∣[(2 : ℤ)] σ) (τ : ℍ) :
    sourceWeightTwoPrimitive h f (σ • τ) =
      sourceWeightTwoPrimitive h' f' τ +
        sourceCuspIntegral f' (mapGL ℚ σ⁻¹ • (∞ : OnePoint ℚ)) ∞ := by
  have he := sourceCuspForm_eichlerIntegral_slash_apply (n := 0) (by norm_num)
    f hh hΓ f' hh' hΓ' σ hf' τ
  simp only [Nat.cast_zero, neg_zero, ModularForm.SL_slash_apply, zpow_zero, mul_one,
    Nat.zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero] at he
  dsimp only [sourceWeightTwoPrimitive]
  rw [he]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

end
end Dubon2026
