import Dubon2026.SourceCuspWeightImageDescent

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning.
The actual cusp-form space is spanned by forms whose original weight-lowered
images are holomorphic fractions over the original cyclotomic Fricke ring.
The fixed-field descent is pulled back through the proved injective map.
The source weight balance k+4a+6b=12m remains explicit; in particular the
geometric weight-two application uses a=b=m=1. This does not remove any
remaining all-weight arithmetic association or higher-continuation gate. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups

theorem span_cuspWeightImage_cyclotomic_fractions_eq_top
    (N : ℕ) [NeZero N] (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      cuspWeightImage Γ k a b m f ∈ holomorphicCyclotomicFrickeFractions N} = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro f
  apply (Submodule.apply_mem_span_image_iff_mem_span
    (cuspWeightImageIntoSpan_injective N Γ hΓ k a b m hk)).mp
  apply (Submodule.span_mono ?_) (cuspWeightImageIntoSpan_descent N Γ hΓ k a b m hk f)
  intro G hG
  obtain ⟨g, hg⟩ := hG.1
  refine ⟨g, ?_, hg⟩
  have hm := (mem_originalFrickeSpan_iff G).mp hG.2
  rw [← hg] at hm
  exact hm

end
end Dubon2026.SourceFricke