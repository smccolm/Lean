import Dubon2026.SourceLaurentSpanDescent
import Dubon2026.SourceOriginalFrickeLaurentField
import Dubon2026.SourceFrickeSpanLaurentRealization

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. A cusp image
already lies in the complex span of original holomorphic Fricke fractions.
If its literal Laurent expansion has cyclotomic coefficients, coefficient
retraction places that expansion in the original cyclotomic Laurent field.
The existing analytic identity theorem then recovers original function
fraction membership, with holomorphy and periodicity derived from the span. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem mem_frickeLaurentFieldK_of_represents_frickeSpan {N : ℕ} [NeZero N]
    {F : ℍ → ℂ} (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    {X : LaurentSeries (kN N)}
    (hX : CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) X) (cuspFunction N F)) :
    X ∈ IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N) := by
  classical
  let E := IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N)
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hF
  choose A hAm hA using fun i => exists_field_laurent_holomorphic_fraction (g i).property
  have hrep := CuspTaylor.Represents.cusp_smul_sum Finset.univ c (fun i _ => hA i)
  rw [hg] at hrep
  have hx : coeffMap (algebraMap (kN N) ℂ) X ∈
      Submodule.span ℂ (coeffMap (algebraMap (kN N) ℂ) '' (E : Set (LaurentSeries (kN N)))) := by
    rw [hX.eq_series hrep]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨A i, hAm i, rfl⟩)
  have hd := mem_span_of_coeffMap_mem_span (algebraMap (kN N) ℂ)
    (E : Set (LaurentSeries (kN N))) X hx
  clear hx hX
  induction hd using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem E
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx =>
    have he : c • x = algebraMap (kN N) (LaurentSeries (kN N)) c * x := by
      ext j
      rw [HahnSeries.coeff_smul, SourceDifferential.algebraMap_laurentSeries_apply_alt,
        HahnSeries.coeff_single_zero_mul]
      rfl
    rw [he]
    exact mul_mem (E.algebraMap_mem c) hx

theorem holomorphicCyclotomicFrickeFractions_of_represents_frickeSpan {N : ℕ} [NeZero N]
    {F : ℍ → ℂ} (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    {X : LaurentSeries (kN N)}
    (hX : CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) X) (cuspFunction N F)) :
    F ∈ holomorphicCyclotomicFrickeFractions N := by
  have hfield := coeffMap_frickeLaurentFieldK_inclusion N
    (mem_frickeLaurentFieldK_of_represents_frickeSpan hF hX)
  obtain ⟨a, b, A, B, ha, hb, hb0, hB0, hAr, hBr, he⟩ :=
    exists_cyclotomic_function_fraction_of_laurent_field hfield
  refine ⟨frickeSpan_holomorphic hF, a, ha, b, hb, hb0, ?_⟩
  have hprod := hX.cusp_mul hBr
  rw [he, div_mul_cancel₀ _ hB0] at hprod
  exact hprod.eq_upperHalfPlane hAr (by exact_mod_cast NeZero.pos N)
    ((frickeSpan_holomorphic hF).mul (cyclotomicLevelRing_holomorphic hb))
    (cyclotomicLevelRing_holomorphic ha)
    ((frickeSpan_periodic hF).mul (cyclotomicLevelRing_periodic hb))
    (cyclotomicLevelRing_periodic ha)

end
end Dubon2026.SourceFricke
