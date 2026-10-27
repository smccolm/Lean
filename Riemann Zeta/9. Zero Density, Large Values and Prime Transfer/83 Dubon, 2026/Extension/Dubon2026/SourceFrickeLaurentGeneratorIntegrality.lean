import Dubon2026.SourceFrickeCyclotomicLaurent
import Dubon2026.SourceCuspLaurentPolynomial
import Dubon2026.SourceFrickeStableMonicV2
import Dubon2026.SourceLaurentIntegralCoefficientImage
import Dubon2026.SourceIntegralTranscendentalSeparability

/-! DUB-17/18 -> rational Fourier spanning -> integral base change of actual
Fricke fractions. The existing finite modular action supplies monic relations
for the actual Fricke generators. Their already proved Laurent realizations
transport those relations; coefficient descent and transport give integrality
over the original cyclotomic j-algebra. The finite generator family and j
transcendence are derived from the literal original series. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold MatrixGroups ModularForm IntermediateField

theorem frickeLaurent_complex_integral (N : ℕ) [NeZero N] (i : FrickeIdx N) :
    IsIntegral (Algebra.adjoin ℂ ({jqNModC ℂ N} : Set (LaurentSeries ℂ)))
      (coeffMap (algebraMap (kN N) ℂ) (frickeLaurentK N i)) := by
  have hm : frickeF N i.1 ∈ (LevelGens.std N).ring := frickeF_mem_levelRing i
  obtain ⟨d, p, hrel⟩ := (LevelGens.std N).ring_monic_j_relation ⟨frickeF N i.1, hm⟩
  exact (represents_frickeLaurentK N i).isIntegral_of_monic_relation
    (represents_jqNModC N) d p hrel

theorem frickeLaurentK_integral (N : ℕ) [NeZero N] (i : FrickeIdx N) :
    IsIntegral (Algebra.adjoin (kN N) ({jqNModC (kN N) N} : Set (LaurentSeries (kN N))))
      (frickeLaurentK N i) := by
  apply isIntegral_adjoin_of_isIntegral_coeffMap (algebraMap (kN N) ℂ)
  rw [coeffMap_jqNModC_kN]
  exact frickeLaurent_complex_integral N i

theorem frickeLaurent_integral_original_constants (N : ℕ) [NeZero N] (i : FrickeIdx N) :
    IsIntegral (Algebra.adjoin (kN N) ({jqNModC ℂ N} : Set (LaurentSeries ℂ)))
      (coeffMap (algebraMap (kN N) ℂ) (frickeLaurentK N i)) := by
  have h := isIntegral_adjoin_coeffMap_of_isIntegral (kN N) (jqNModC (kN N) N)
    (frickeLaurentK N i) (frickeLaurentK_integral N i)
  rwa [coeffMap_jqNModC_kN] at h

/-- The literal expanded j and original cyclotomic Fricke Laurent series. -/
def frickeLaurentGenerators (N : ℕ) [NeZero N] : Set (LaurentSeries ℂ) :=
  insert (jqNModC ℂ N)
    (Set.range fun i : FrickeIdx N => coeffMap (algebraMap (kN N) ℂ) (frickeLaurentK N i))

theorem frickeLaurentGenerators_finite (N : ℕ) [NeZero N] : (frickeLaurentGenerators N).Finite :=
  (Set.finite_range _).insert _

theorem frickeLaurentGenerators_coeffRange (N : ℕ) [NeZero N] :
    frickeLaurentGenerators N ⊆ (coeffMap (algebraMap (kN N) ℂ)).fieldRange := by
  rintro z (rfl | ⟨i, rfl⟩)
  · exact ⟨jqNModC (kN N) N, coeffMap_jqNModC_kN N⟩
  · exact ⟨frickeLaurentK N i, rfl⟩

theorem frickeLaurentGenerators_integral (N : ℕ) [NeZero N] :
    ∀ z ∈ frickeLaurentGenerators N,
      IsIntegral (Algebra.adjoin (kN N) ({jqNModC ℂ N} : Set (LaurentSeries ℂ))) z := by
  rintro z (rfl | ⟨i, rfl⟩)
  · exact isIntegral_algebraMap (x :=
      (⟨jqNModC ℂ N, Algebra.self_mem_adjoin_singleton (kN N) (jqNModC ℂ N)⟩ :
        Algebra.adjoin (kN N) ({jqNModC ℂ N} : Set (LaurentSeries ℂ))))
  · exact frickeLaurent_integral_original_constants N i

theorem transcendental_frickeLaurent_j (N : ℕ) [NeZero N] :
    Transcendental ℂ (jqNModC ℂ N) :=
  IntegralJCoordinate.transcendental_qExpand_jqModC ℂ N

end
end Dubon2026.SourceFricke