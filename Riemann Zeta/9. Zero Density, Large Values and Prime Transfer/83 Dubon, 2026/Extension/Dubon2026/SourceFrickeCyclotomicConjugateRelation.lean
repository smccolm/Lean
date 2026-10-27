import Dubon2026.SourceFrickeCyclotomicAnalyticTransport
import Dubon2026.SourceCuspLaurentLinearRelations

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> cyclotomic conjugation compatible with cusp images. This
relation records literal Laurent conjugation of actual functions. Existence
for original holomorphic Fricke fractions was proved analytically; uniqueness
and the product/power rules follow from their actual Laurent germs. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

/-- Literal coefficient conjugation between the cusp germs of actual functions. -/
def CyclotomicConjugates {N : ℕ} (σ : kN N ≃ₐ[ℚ] kN N) (F G : ℍ → ℂ) : Prop :=
  ∃ A : LaurentSeries (kN N),
    CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) A) (cuspFunction N F) ∧
    CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ)
      (coeffMap σ.toRingEquiv.toRingHom A)) (cuspFunction N G)

theorem exists_cyclotomicConjugates {N : ℕ} [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) {F : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N) :
    ∃ G ∈ holomorphicCyclotomicFrickeFractions N, CyclotomicConjugates σ F G := by
  obtain ⟨A, G, hA, hG, hAG⟩ := exists_holomorphic_cyclotomic_conjugate N σ hF
  exact ⟨G, hG, A, hA, hAG⟩

theorem CyclotomicConjugates.unique {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N}
    {F G H : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G) (hFH : CyclotomicConjugates σ F H)
    (hG : G ∈ holomorphicCyclotomicFrickeFractions N)
    (hH : H ∈ holomorphicCyclotomicFrickeFractions N) : G = H := by
  obtain ⟨A, hA, hAG⟩ := hFG
  obtain ⟨B, hB, hBH⟩ := hFH
  have he : A = B := (coeffMap (algebraMap (kN N) ℂ)).injective (hA.eq_series hB)
  subst B
  exact hAG.eq_upperHalfPlane hBH (by exact_mod_cast NeZero.pos N) hG.1 hH.1
    (holomorphicCyclotomicFrickeFractions_periodic hG)
    (holomorphicCyclotomicFrickeFractions_periodic hH)

theorem CyclotomicConjugates.add {N : ℕ} {σ : kN N ≃ₐ[ℚ] kN N}
    {F G H I : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G) (hHI : CyclotomicConjugates σ H I) :
    CyclotomicConjugates σ (F + H) (G + I) := by
  obtain ⟨A, hA, hAG⟩ := hFG
  obtain ⟨B, hB, hBI⟩ := hHI
  exact ⟨A + B, by simpa only [map_add] using hA.cusp_add hB,
    by simpa only [map_add] using hAG.cusp_add hBI⟩

theorem CyclotomicConjugates.mul {N : ℕ} {σ : kN N ≃ₐ[ℚ] kN N}
    {F G H I : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G) (hHI : CyclotomicConjugates σ H I) :
    CyclotomicConjugates σ (F * H) (G * I) := by
  obtain ⟨A, hA, hAG⟩ := hFG
  obtain ⟨B, hB, hBI⟩ := hHI
  exact ⟨A * B, by simpa only [map_mul] using hA.cusp_mul hB,
    by simpa only [map_mul] using hAG.cusp_mul hBI⟩

theorem CyclotomicConjugates.pow {N : ℕ} {σ : kN N ≃ₐ[ℚ] kN N}
    {F G : ℍ → ℂ} (hFG : CyclotomicConjugates σ F G) (n : ℕ) :
    CyclotomicConjugates σ (F ^ n) (G ^ n) := by
  obtain ⟨A, hA, hAG⟩ := hFG
  exact ⟨A ^ n, by simpa only [map_pow] using hA.cusp_pow n,
    by simpa only [map_pow] using hAG.cusp_pow n⟩

theorem CyclotomicConjugates.const {N : ℕ} (σ : kN N ≃ₐ[ℚ] kN N) (c : kN N) :
    CyclotomicConjugates σ (fun _ : ℍ => (c : ℂ)) (fun _ : ℍ => (σ c : ℂ)) := by
  refine ⟨algebraMap (kN N) (LaurentSeries (kN N)) c, ?_, ?_⟩
  · simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single] using
      CuspTaylor.represents_cusp_const N (c : ℂ)
  · simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single] using
      CuspTaylor.represents_cusp_const N (σ c : ℂ)

theorem CyclotomicConjugates.j {N : ℕ} [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N) :
    CyclotomicConjugates σ JMultiplicity.jf JMultiplicity.jf := by
  refine ⟨jqNModC (kN N) N, ?_, ?_⟩
  · rw [coeffMap_jqNModC_kN]
    exact represents_jqNModC N
  · rw [coeffMap_jqNModC_aut, coeffMap_jqNModC_kN]
    exact represents_jqNModC N

theorem CyclotomicConjugates.fricke {N : ℕ} [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N)
    (s : ℕ) (hs : s.Coprime N) (hσ : σ (zetaK N) = zetaK N ^ s) (i : FrickeIdx N) :
    CyclotomicConjugates σ (frickeF N i.1) (frickeF N (cyclotomicFrickeIndex s hs i).1) := by
  refine ⟨frickeLaurentK N i, represents_frickeLaurentK N i, ?_⟩
  rw [coeffMap_frickeLaurentK_aut N σ s hs hσ]
  exact represents_frickeLaurentK N _

end
end Dubon2026.SourceFricke
