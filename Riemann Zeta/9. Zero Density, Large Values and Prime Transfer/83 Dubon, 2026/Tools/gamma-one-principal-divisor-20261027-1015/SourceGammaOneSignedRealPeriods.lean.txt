import Dubon2026.SourceGammaOneRealPeriodSurjectivity
import Dubon2026.SourceWeightTwoSignedForms

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
integral Petersson duality. Realize a real character on the signed group by
an original Gamma1 cusp form. Restriction and the already proved equality of
real character values on elements with equal squares transport the existing
original real-period surjectivity; no new dimension argument is needed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.SignedPeriods
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups GammaOne
variable (Γ : Subgroup SL(2, ℤ))

/-- Restriction of the actual real character along the subgroup inclusion. -/
def restrictReal (φ : Additive (plusMinus Γ) →+ ℝ) : Additive Γ →+ ℝ where
  toFun a := φ (Additive.ofMul ⟨a.toMul.val, le_plusMinus Γ a.toMul.property⟩)
  map_zero' := map_zero φ
  map_add' a b := map_add φ
    (Additive.ofMul ⟨a.toMul.val, le_plusMinus Γ a.toMul.property⟩)
    (Additive.ofMul ⟨b.toMul.val, le_plusMinus Γ b.toMul.property⟩)

theorem restrictReal_representative (φ : Additive (plusMinus Γ) →+ ℝ) (γ : plusMinus Γ) :
    restrictReal Γ φ (Additive.ofMul (CentralSign.representative Γ γ)) =
      φ (Additive.ofMul γ) := by
  apply CentralSign.real_character_eq_of_square_eq (plusMinus Γ) φ
  apply Subtype.ext
  change (CentralSign.representative Γ γ).val ^ 2 = γ.val ^ 2
  rcases CentralSign.representative_spec Γ γ with h | h <;>
    simp only [h, sq, neg_mul, mul_neg, neg_neg]

theorem exists_original_cuspForm_of_signed_real_character (N : ℕ) [NeZero N]
    (φ : Additive (plusMinus (Gamma1 N)) →+ ℝ)
    (hφ : ∀ γ : plusMinus (Gamma1 N), γ.val.val.trace ^ 2 = 4 →
      φ (Additive.ofMul γ) = 0) :
    ∃ k : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
      ∀ γ : plusMinus (Gamma1 N),
        (sourceWeightTwoPeriodValue (plusMinus (Gamma1 N)) (SignedForms.extend (Gamma1 N) k) γ).re =
          φ (Additive.ofMul γ) := by
  have hp : ∀ γ : Gamma1 N, γ.val.val.trace ^ 2 = 4 →
      restrictReal (Gamma1 N) φ (Additive.ofMul γ) = 0 :=
    fun γ hγ => hφ ⟨γ.val, le_plusMinus (Gamma1 N) γ.property⟩ hγ
  obtain ⟨k, hk⟩ := sourceGamma1_exists_cuspForm_of_real_parabolic_character N
    (restrictReal (Gamma1 N) φ) hp
  refine ⟨k, fun γ => ?_⟩
  rw [SignedForms.period_extend_representative, hk, restrictReal_representative]

end
end Dubon2026.SourceFunctionField.GammaOne.SignedPeriods
