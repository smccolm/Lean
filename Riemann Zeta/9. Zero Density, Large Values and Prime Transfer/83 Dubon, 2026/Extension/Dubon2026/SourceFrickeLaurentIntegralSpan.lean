import Dubon2026.SourceFrickeComplexFractionLaurent
import Dubon2026.SourceLaurentIntegralConstantSpan
import Dubon2026.SourceFrickeModularOrbitV2

/-! DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
character realization -> differential/cusp comparison -> rational Fourier
spanning -> integral base change of the original Fricke fractions.
The actual modular orbit gives a Fricke fraction and a monic j-relation. Its
Laurent realization then consumes the integral-span theorem with all finite
generator, coefficient-field and transcendence hypotheses discharged for the
original Fricke series. Recovery of holomorphic summand functions and rational
Fourier spanning are subsequent obligations. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold MatrixGroups ModularForm

theorem frickeLaurent_integral_mem_span {N : ℕ} [NeZero N] {X : LaurentSeries ℂ}
    (hX : X ∈ IntermediateField.adjoin ℂ (frickeLaurentGenerators N))
    (hI : IsIntegral (Algebra.adjoin ℂ ({jqNModC ℂ N} : Set (LaurentSeries ℂ))) X) :
    X ∈ Submodule.span ℂ
      (ConstantDescent.RSet (kN N) {jqNModC ℂ N} (frickeLaurentGenerators N)) := by
  exact ConstantDescent.mem_span_integral_generated_of_complex (kN N) (jqNModC ℂ N)
    (frickeLaurentGenerators N) (transcendental_frickeLaurent_j N) (Set.mem_insert _ _)
    (frickeLaurentGenerators_finite N) (frickeLaurentGenerators_integral N)
    (frickeLaurentGenerators_coeffRange N) hX hI

theorem exists_fricke_laurent_integral_span_of_principal_invariant
    {N : ℕ} [NeZero N] (F : ℍ → ℂ) (hF : MDiff F)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ⇑CuspForm.discriminant ^ m)) :
    ∃ X : LaurentSeries ℂ, CuspTaylor.Represents X (cuspFunction N F) ∧
      X ∈ Submodule.span ℂ
        (ConstantDescent.RSet (kN N) {jqNModC ℂ N} (frickeLaurentGenerators N)) := by
  obtain ⟨⟨a, b, hb0, hrel⟩, d, p, hmonic⟩ :=
    exists_fraction_and_monic_j_of_principal_invariant F hF hinv hpb
  have hbfun0 : (b : ℍ → ℂ) ≠ 0 := fun h => hb0 (Subtype.ext h)
  obtain ⟨X, hX, hrep⟩ := exists_complex_fricke_fraction_represents a.property b.property hbfun0 hrel
  have hI := hrep.isIntegral_of_monic_relation (represents_jqNModC N) d p hmonic
  exact ⟨X, hrep, frickeLaurent_integral_mem_span hX hI⟩

end
end Dubon2026.SourceFricke