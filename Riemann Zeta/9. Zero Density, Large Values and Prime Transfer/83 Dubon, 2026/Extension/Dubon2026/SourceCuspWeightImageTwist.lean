import Dubon2026.SourceCuspWeightImageSpan
import Dubon2026.SourceFrickeTwistCuspConditions

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> stability of the actual cusp-form image under original-field coefficient
twists. Every elliptic, cusp and subgroup condition is derived for the
twisted original image and consumed by the proved characterization to
construct another actual cusp form of the same weight and subgroup. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField SourceFunctionField.CuspWeightCriterion ModularForm
open scoped Manifold MatrixGroups ModularForm

theorem exists_cuspWeightImage_eq_twist (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ f' : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k,
      cuspWeightImage Γ k a b m f' =
        (frickeCoefficientTwist N σ (cuspWeightImageElement N Γ hΓ k a b m hk f) : ℍ → ℂ) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  let V := cuspWeightImageElement N Γ hΓ k a b m hk f
  have hhol : MDiff (V : ℍ → ℂ) := mdifferentiable_cuspWeightImage Γ k a b m f
  obtain ⟨h1, h2, h3, h4⟩ := (CuspWeightCriterion.main Γ k a b m hk (V : ℍ → ℂ) hhol).mp
    ⟨f, cuspWeightImage_mul_discriminant Γ k a b m f⟩
  have ht1 := frickeCoefficientTwist_E4_divisibility N σ V m a h1
  have ht2 := frickeCoefficientTwist_E6_divisibility N σ V m b h2
  have ht3 := frickeCoefficientTwist_preserves_all_cusps N σ V m h3
  have ht4 := frickeCoefficientTwist_preserves_subgroup_invariance N σ Γ V h4
  obtain ⟨f', hf'⟩ := (CuspWeightCriterion.main Γ k a b m hk
    (frickeCoefficientTwist N σ V : ℍ → ℂ)
    (frickeSpan_holomorphic (frickeCoefficientTwist N σ V).property)).mpr ⟨ht1, ht2, ht3, ht4⟩
  refine ⟨f', ?_⟩
  funext τ
  change f' τ * (E₄ τ ^ a * E₆ τ ^ b) / discriminant τ ^ m =
    (frickeCoefficientTwist N σ V : ℍ → ℂ) τ
  rw [hf' τ, mul_div_cancel_right₀ _ (pow_ne_zero _ (discriminant_ne_zero τ))]

end
end Dubon2026.SourceFricke