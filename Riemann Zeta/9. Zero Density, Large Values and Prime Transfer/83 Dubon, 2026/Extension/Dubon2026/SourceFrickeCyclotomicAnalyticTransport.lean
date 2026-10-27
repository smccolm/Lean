import Dubon2026.SourceOriginalFrickeLaurentField
import Dubon2026.SourceFrickeIntegralHolomorphicRepresentative

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> cyclotomic coefficient conjugation. Conjugate the literal
Laurent germ inside the original field, preserve its derived integrality,
and consume the existing holomorphic representative theorem. The output
is an actual holomorphic original Fricke fraction, not a formal series
or an assumed analytic action. Modular and cusp compatibility remain. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem exists_holomorphic_cyclotomic_conjugate (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) {F : ℍ → ℂ}
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N) :
    ∃ (A : LaurentSeries (kN N)) (G : ℍ → ℂ),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) A) (cuspFunction N F) ∧
      G ∈ holomorphicCyclotomicFrickeFractions N ∧
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ)
        (coeffMap σ.toRingEquiv.toRingHom A)) (cuspFunction N G) := by
  obtain ⟨A, hAm, hA⟩ := exists_field_laurent_holomorphic_fraction hF
  have hI := isIntegral_laurent_holomorphic_fraction hF hA
  have hYfield := coeffMap_frickeLaurentFieldK_inclusion N
    (coeffMap_frickeLaurentFieldK_aut N σ hAm)
  have hYint := isIntegral_adjoin_coeffMap_of_isIntegral (kN N) (jqNModC (kN N) N)
    (coeffMap σ.toRingEquiv.toRingHom A) (isIntegral_jAlgebraK_coeffMap_aut N σ hI)
  rw [coeffMap_jqNModC_kN] at hYint
  obtain ⟨G, a, b, ha, hb, hb0, hG, he, hrep, _⟩ :=
    exists_holomorphic_cyclotomic_fraction_of_integral_laurent ⟨hYfield, hYint⟩
  exact ⟨A, G, hA, ⟨hG, a, ha, b, hb, hb0, he⟩, hrep⟩

end
end Dubon2026.SourceFricke
