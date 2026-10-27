import Dubon2026.SourceLaurentTwistOrder
import Dubon2026.SourceCuspVanishingOrder

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> cusp stability under coefficient descent. The actual discriminant has
cyclotomic Laurent coefficients, so coefficient twists preserve the cusp
order of F times every fixed discriminant power. This proves preservation
of cusp vanishing without treating the positive-weight discriminant as a
weight-zero Fricke fraction or assuming continuity of field automorphisms. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem coeffMap_cyclotomic_fixed (N : ℕ) (σ : ℂ ≃ₐ[kN N] ℂ)
    (A : LaurentSeries (kN N)) :
    coeffMap σ.toRingHom (coeffMap (algebraMap (kN N) ℂ) A) =
      coeffMap (algebraMap (kN N) ℂ) A := by
  ext n
  simp only [coeffMap_coeff]
  change σ (algebraMap (kN N) ℂ (A.coeff n)) = _
  exact σ.commutes _

theorem coeffMap_discriminant_fixed (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ) :
    coeffMap σ.toRingHom (qExpansion N (⇑CuspForm.discriminant : ℍ → ℂ) : LaurentSeries ℂ) =
      (qExpansion N (⇑CuspForm.discriminant : ℍ → ℂ) : LaurentSeries ℂ) := by
  rw [← coeffMap_discriminantLaurentK]
  exact coeffMap_cyclotomic_fixed N σ _

theorem exists_fricke_twist_laurent_mul_discriminant (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (m : ℕ) : ∃ A : LaurentSeries ℂ,
      CuspTaylor.Represents A
        (cuspFunction N ((F : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m)) ∧
      CuspTaylor.Represents (coeffMap σ.toRingHom A)
        (cuspFunction N ((frickeCoefficientTwist N σ F : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m)) := by
  obtain ⟨A, hA, hT⟩ := exists_fricke_twist_laurent N σ F
  refine ⟨A * (qExpansion N (⇑CuspForm.discriminant : ℍ → ℂ) : LaurentSeries ℂ) ^ m,
    hA.cusp_mul ((represents_discriminant_width N).cusp_pow m), ?_⟩
  rw [map_mul, map_pow, coeffMap_discriminant_fixed]
  exact hT.cusp_mul ((represents_discriminant_width N).cusp_pow m)

theorem frickeCoefficientTwist_cusp_order_mul_discriminant (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (m : ℕ) :
    meromorphicOrderAt
      (cuspFunction N ((frickeCoefficientTwist N σ F : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m)) 0 =
    meromorphicOrderAt (cuspFunction N ((F : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m)) 0 := by
  obtain ⟨A, hA, hT⟩ := exists_fricke_twist_laurent_mul_discriminant N σ F m
  rw [hT.orderTop, hA.orderTop, coeffMap_orderTop]

theorem frickeCoefficientTwist_isZeroAtImInfty_mul_discriminant_iff (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (m : ℕ) :
    IsZeroAtImInfty ((frickeCoefficientTwist N σ F : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m) ↔
      IsZeroAtImInfty ((F : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m) := by
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hd : MDiff (⇑CuspForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'
  rw [isZeroAtImInfty_iff_cusp_order_pos hh
      ((frickeSpan_holomorphic (frickeCoefficientTwist N σ F).property).mul
        (hd.pow m))
      (periodic_mul_discriminant (frickeSpan_periodic (frickeCoefficientTwist N σ F).property) m),
    isZeroAtImInfty_iff_cusp_order_pos hh
      ((frickeSpan_holomorphic F.property).mul (hd.pow m))
      (periodic_mul_discriminant (frickeSpan_periodic F.property) m),
    frickeCoefficientTwist_cusp_order_mul_discriminant]

end
end Dubon2026.SourceFricke