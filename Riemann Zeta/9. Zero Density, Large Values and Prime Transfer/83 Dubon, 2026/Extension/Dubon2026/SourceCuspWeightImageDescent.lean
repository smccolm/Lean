import Dubon2026.SourceOriginalFrickeSpanDescent

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> original-field descent of the actual cusp image. Use the original
weight-lowering map with its proved span membership and injectivity. Its
actual range is stable by the previously constructed same-weight cusp form,
so the proved fixed-field descent applies with no stability assumption left. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups

/-- The original weight-lowering map with codomain restricted by proved Fricke-span membership. -/
def cuspWeightImageIntoSpan (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) :
    CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) :=
  (cuspWeightImage Γ k a b m).codRestrict _
    (cuspWeightImage_mem_frickeSpan N Γ hΓ k a b m hk)

theorem cuspWeightImageIntoSpan_injective (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) :
    Function.Injective (cuspWeightImageIntoSpan N Γ hΓ k a b m hk) := by
  intro f g he
  exact cuspWeightImage_injective Γ k a b m (congrArg Subtype.val he)

theorem cuspWeightImageIntoSpan_twist_mem_range (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m)
    {F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)}
    (hF : F ∈ LinearMap.range (cuspWeightImageIntoSpan N Γ hΓ k a b m hk)) :
    frickeCoefficientTwist N σ F ∈ LinearMap.range (cuspWeightImageIntoSpan N Γ hΓ k a b m hk) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, hg⟩ := exists_cuspWeightImage_eq_twist N σ Γ hΓ k a b m hk f
  exact ⟨g, Subtype.ext hg⟩

theorem cuspWeightImageIntoSpan_descent (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspWeightImageIntoSpan N Γ hΓ k a b m hk f ∈ Submodule.span ℂ
      {G | G ∈ LinearMap.range (cuspWeightImageIntoSpan N Γ hΓ k a b m hk) ∧ G ∈ originalFrickeSpan N} := by
  exact mem_span_originalFrickeSpan_of_twist_stable N _
    (fun σ _ hF => cuspWeightImageIntoSpan_twist_mem_range N σ Γ hΓ k a b m hk hF)
    ⟨f, rfl⟩

end
end Dubon2026.SourceFricke