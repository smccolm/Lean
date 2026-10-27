import Dubon2026.SourceCyclotomicFractionCovariance
import Dubon2026.SourceCuspVanishingOrder

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> actual cusp-condition transport. The literal discriminant is
fixed by cyclotomic conjugation; coefficient injectivity preserves Laurent
order. The previously proved modular lifts then transport vanishing at every
cusp, without assuming continuity of an abstract field automorphism. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem CyclotomicConjugates.discriminant {N : ℕ} [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N) :
    CyclotomicConjugates σ (⇑CuspForm.discriminant : ℍ → ℂ) ⇑CuspForm.discriminant := by
  refine ⟨discriminantLaurentK N, ?_, ?_⟩
  · rw [coeffMap_discriminantLaurentK]
    exact represents_discriminant_width N
  · change CuspTaylor.Represents
      (coeffMap ((algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom) (discriminantLaurentK N)) _
    rw [coeffMap_discriminantLaurentK_ringHom]
    exact represents_discriminant_width N

theorem CyclotomicConjugates.cusp_order {N : ℕ} {σ : kN N ≃ₐ[ℚ] kN N}
    {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G) :
    meromorphicOrderAt (cuspFunction N G) 0 = meromorphicOrderAt (cuspFunction N F) 0 := by
  obtain ⟨A, hA, hAG⟩ := hFG
  rw [hAG.orderTop, hA.orderTop, coeffMap_orderTop, coeffMap_orderTop, coeffMap_orderTop]

theorem CyclotomicConjugates.isZeroAtImInfty_mul_discriminant_iff {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) (m : ℕ) :
    IsZeroAtImInfty (G * ⇑CuspForm.discriminant ^ m) ↔
      IsZeroAtImInfty (F * ⇑CuspForm.discriminant ^ m) := by
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hd : MDiff (⇑CuspForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'
  rw [isZeroAtImInfty_iff_cusp_order_pos hh (hG.1.mul (hd.pow m))
      (periodic_mul_discriminant (holomorphicCyclotomicFrickeFractions_periodic hG) m),
    isZeroAtImInfty_iff_cusp_order_pos hh (hF.1.mul (hd.pow m))
      (periodic_mul_discriminant (holomorphicCyclotomicFrickeFractions_periodic hF) m),
    (hFG.mul ((CyclotomicConjugates.discriminant σ).pow m)).cusp_order]

theorem CyclotomicConjugates.all_cusps {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G)
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N) (m : ℕ)
    (hFcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * ⇑CuspForm.discriminant ^ m)) :
    ∀ A : SL(2, ℤ), IsZeroAtImInfty ((G ∘ (A • ·)) * ⇑CuspForm.discriminant ^ m) := by
  intro A
  obtain ⟨A', hrel⟩ := hFG.exists_modular hF hG A
  have hFA : F ∘ (A' • ·) ∈ holomorphicCyclotomicFrickeFractions N := by
    simpa only [sl_smul_def, inv_inv, Function.comp_def] using
      smul_mem_holomorphicCyclotomicFrickeFractions A'⁻¹ hF
  have hGA : G ∘ (A • ·) ∈ holomorphicCyclotomicFrickeFractions N := by
    simpa only [sl_smul_def, inv_inv, Function.comp_def] using
      smul_mem_holomorphicCyclotomicFrickeFractions A⁻¹ hG
  exact (hrel.isZeroAtImInfty_mul_discriminant_iff hFA hGA m).mpr (hFcusp A')

end
end Dubon2026.SourceFricke
