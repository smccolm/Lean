import Dubon2026.SourceCuspWeightImage

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> actual cusp-image descent. Consume the original cusp form and the exact
weight-lowering criterion to derive principal-level invariance and all cusp
pole bounds. The actual function-spanning theorem then places its image in
the original complex Fricke span; no image-membership premise is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField SourceFunctionField.CuspWeightCriterion
open scoped Manifold MatrixGroups ModularForm

theorem cuspWeightImage_mem_frickeSpan (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspWeightImage Γ k a b m f ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hhol := mdifferentiable_cuspWeightImage Γ k a b m f
  obtain ⟨_, _, hcusp, hinv⟩ := (CuspWeightCriterion.main Γ k a b m hk _ hhol).mp
    ⟨f, cuspWeightImage_mul_discriminant Γ k a b m f⟩
  apply mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant _ hhol
    (fun γ hγ τ => hinv γ (hΓ hγ) τ)
  intro A
  refine ⟨m, ?_⟩
  simpa only [CuspForm.coe_discriminant] using (hcusp A).isBoundedAtImInfty

/-- The original cusp-form image, with its proved membership in the complex Fricke span. -/
def cuspWeightImageElement (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) :=
  ⟨cuspWeightImage Γ k a b m f, cuspWeightImage_mem_frickeSpan N Γ hΓ k a b m hk f⟩

end
end Dubon2026.SourceFricke