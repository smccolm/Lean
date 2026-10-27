import Dubon2026.SourceFrickeLaurentFieldConjugation
import Dubon2026.SourceFrickePrincipalInvariance
import Dubon2026.SourceMeromorphicCuspPoleClearing

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> cyclotomic conjugation. An actual holomorphic original Fricke
fraction has a Laurent germ in the original generated cyclotomic field,
integral over its j algebra. Principal invariance and all cusp pole bounds
are derived from the original fraction; no monic relation is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem exists_field_laurent_cyclotomic_levelRing {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ cyclotomicLevelRing N) :
    ∃ A ∈ IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) A) (cuspFunction N F) := by
  induction hF using Algebra.adjoin_induction with
  | mem F hF =>
    rcases hF with rfl | ⟨i, rfl⟩
    · refine ⟨jqNModC (kN N) N, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _), ?_⟩
      rw [coeffMap_jqNModC_kN]
      exact represents_jqNModC N
    · exact ⟨frickeLaurentK N i,
        IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩),
        represents_frickeLaurentK N i⟩
  | algebraMap c =>
    refine ⟨algebraMap (kN N) (LaurentSeries (kN N)) c,
      IntermediateField.algebraMap_mem _ c, ?_⟩
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single]
    simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt] using
      CuspTaylor.represents_cusp_const N (c : ℂ)
  | add F G _ _ hF hG =>
    obtain ⟨A, hAm, hA⟩ := hF
    obtain ⟨B, hBm, hB⟩ := hG
    exact ⟨A + B, add_mem hAm hBm, by rw [map_add]; exact hA.cusp_add hB⟩
  | mul F G _ _ hF hG =>
    obtain ⟨A, hAm, hA⟩ := hF
    obtain ⟨B, hBm, hB⟩ := hG
    exact ⟨A * B, mul_mem hAm hBm, by rw [map_mul]; exact hA.cusp_mul hB⟩

theorem exists_field_laurent_holomorphic_fraction {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N) :
    ∃ A ∈ IntermediateField.adjoin (kN N) (frickeLaurentGeneratorsK N),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) A) (cuspFunction N F) := by
  obtain ⟨_, a, ha, b, hb, hb0, he⟩ := hF
  obtain ⟨A, hAm, hA⟩ := exists_field_laurent_cyclotomic_levelRing ha
  obtain ⟨B, hBm, hB⟩ := exists_field_laurent_cyclotomic_levelRing hb
  have hB0 := hB.ne_zero_of_function_ne_zero (by exact_mod_cast NeZero.pos N)
    (cyclotomicLevelRing_holomorphic hb) (cyclotomicLevelRing_periodic hb) hb0
  exact ⟨A / B, div_mem hAm hBm, by rw [map_div₀]; exact hA.cusp_of_mul_eq hB hB0 he⟩

theorem isIntegral_laurent_holomorphic_fraction {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N) {A : LaurentSeries (kN N)}
    (hA : CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) A) (cuspFunction N F)) :
    IsIntegral (Algebra.adjoin (kN N)
      ({jqNModC (kN N) N} : Set (LaurentSeries (kN N)))) A := by
  have hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m) := by
    intro γ
    have hG : F ∘ (γ • ·) ∈ holomorphicCyclotomicFrickeFractions N := by
      simpa only [sl_smul_def, inv_inv, Function.comp_def] using
        smul_mem_holomorphicCyclotomicFrickeFractions γ⁻¹ hF
    obtain ⟨B, _, hB⟩ := exists_field_laurent_holomorphic_fraction hG
    exact exists_bounded_mul_discriminant_of_meromorphic
      (holomorphicCyclotomicFrickeFractions_periodic hG) hB.meromorphicAt
  obtain ⟨_, d, p, hm⟩ := exists_fraction_and_monic_j_of_principal_invariant F hF.1
    (principalInvariant_frickeSpan (Submodule.subset_span hF)) hpb
  apply isIntegral_adjoin_of_isIntegral_coeffMap (algebraMap (kN N) ℂ)
  rw [coeffMap_jqNModC_kN]
  exact hA.isIntegral_of_monic_relation (represents_jqNModC N) d p hm

end
end Dubon2026.SourceFricke
