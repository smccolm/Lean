import Dubon2026.OriginalOutsideClassExactSequence
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # Finite-stage H1 vanishing for the original class quotient

The already proved original class H1 and outside-unit H2 vanishing give
the first class-formation input for the literal quotient at fixed support.
This does not assert class formation or vanishing for Hom coefficients.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Actual full classes modulo outside units have zero H1 at the original unramified support. -/
theorem originalClassesModOutside_first_zero
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Limits.IsZero (groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 1) := by
  let hX := originalOutsideClassShortComplex_shortExact K L S hS
  have hu2 := originalOutsideUnit_second_zero_of_unramified K L S hS hu
  have he := groupCohomology.mapShortComplex₃_exact hX (i := 1) rfl
  haveI : Epi ((groupCohomology.functor ℤ Gal(L/K) 1).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) := he.epi_f (hu2.eq_zero_of_tgt _)
  apply Limits.IsZero.of_epi_eq_zero ((groupCohomology.functor ℤ Gal(L/K) 1).map
    (originalIdeleClassesModOutsideRepHom K L S hS))
  exact (originalIdeleClass_finiteGalois_first_zero K L).eq_zero_of_src _

end
end Dubon2026
