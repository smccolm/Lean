import Dubon2026.SourceWeightTwoSignedReciprocity

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
integral Petersson duality. Lift each actual original integer period to the
signed group using the same endpoint functionals, then extend by the literal
integer span. This supplies the missing direction for the existing proved
restriction of signed periods; no lattice equivalence is postulated. -/
namespace Dubon2026.SourceFunctionField.GammaOne.SignedForms
noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups GammaOne
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

theorem period_extend_member (f : CuspForm (Γ.map (mapGL ℝ)) 2) (γ : Γ) :
    sourceWeightTwoPeriodValue (plusMinus Γ) (extend Γ f)
      ⟨γ.val, le_plusMinus Γ γ.property⟩ = sourceWeightTwoPeriodValue Γ f γ := by
  rw [← sourceWeightTwoAlong_smul (plusMinus Γ)
    ⟨γ.val, le_plusMinus Γ γ.property⟩ UpperHalfPlane.I, along_extend]
  exact sourceWeightTwoAlong_smul Γ γ UpperHalfPlane.I f

theorem exists_signed_integral_lattice_lift
    (Λ : Module.Dual ℂ (CuspForm (Γ.map (mapGL ℝ)) 2))
    (hΛ : Λ ∈ sourceWeightTwoIntegralLattice Γ) :
    ∃ L ∈ sourceWeightTwoIntegralLattice (plusMinus Γ),
      ∀ g : CuspForm (Γ.map (mapGL ℝ)) 2, L (extend Γ g) = Λ g := by
  induction hΛ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, rfl⟩ := hx
    refine ⟨sourceWeightTwoDualPeriod (plusMinus Γ) ⟨γ.val, le_plusMinus Γ γ.property⟩,
      sourceWeightTwoDualPeriod_mem _ _, fun g => ?_⟩
    simp only [sourceWeightTwoDualPeriod_apply, period_extend_member]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨L, hL, he⟩ := hx
    obtain ⟨M, hM, hf⟩ := hy
    exact ⟨L + M, Submodule.add_mem _ hL hM, fun g => by
      simp only [LinearMap.add_apply, he, hf]⟩
  | smul n x _ hx =>
    obtain ⟨L, hL, he⟩ := hx
    exact ⟨n • L, Submodule.smul_mem _ n hL, fun g => by
      simp only [LinearMap.smul_apply, he]⟩

end
end Dubon2026.SourceFunctionField.GammaOne.SignedForms
