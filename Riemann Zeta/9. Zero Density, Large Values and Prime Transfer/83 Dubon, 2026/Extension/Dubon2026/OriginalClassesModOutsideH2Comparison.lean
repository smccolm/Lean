import Dubon2026.OriginalOutsideUnitH3Vanishing
import Dubon2026.OriginalClassesModOutsideH1

/-! # Original full classes and outside-unit quotients have the same finite H2

Proved outside-unit H2 and H3 vanishing remove the cyclicity restriction
from the literal quotient comparison. The existing arbitrary finite-Galois
full-class H2 finiteness and degree-divisibility bound now apply to the
actual class-formation coefficient on DUB-17's global-duality route.
This comparison does not construct the normalized invariant map.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)

include hu

/-- The literal full-class quotient induces an isomorphism on H2 for every original finite Galois extension unramified outside S. -/
theorem originalClassesModOutside_H2_isIso :
    IsIso ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) := by
  have hu2 := originalOutsideUnit_second_zero_of_unramified K L S hS hu
  have hu3 := originalOutsideUnit_third_zero_of_unramified K L S hS hu
  let hX := originalOutsideClassShortComplex_shortExact K L S hS
  haveI : Mono ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) :=
    (groupCohomology.mapShortComplex₂_exact hX 2).mono_g (hu2.eq_zero_of_src _)
  haveI : Epi ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalIdeleClassesModOutsideRepHom K L S hS)) :=
    (groupCohomology.mapShortComplex₃_exact hX (i := 2) rfl).epi_f (hu3.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The original H2 equivalence whose forward map is exactly the actual quotient map. -/
def originalClassesModOutsideH2Iso :
    groupCohomology (originalIdeleClassRep K L) 2 ≅
      groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2 := by
  let f : groupCohomology (originalIdeleClassRep K L) 2 ⟶
      groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2 :=
    (groupCohomology.functor ℤ Gal(L/K) 2).map
    (originalIdeleClassesModOutsideRepHom K L S hS)
  haveI : IsIso f := originalClassesModOutside_H2_isIso K L S hS hu
  exact asIso f

/-- Every original finite quotient H2 class has exactly one original full-class H2 preimage. -/
theorem originalClassesModOutside_H2_unique_full_class
    (x : groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) :
    ∃! y : groupCohomology (originalIdeleClassRep K L) 2,
      (groupCohomology.functor ℤ Gal(L/K) 2).map
        (originalIdeleClassesModOutsideRepHom K L S hS) y = x :=
  (originalClassesModOutsideH2Iso K L S hS hu).toLinearEquiv.bijective.existsUnique x

/-- Original class-quotient H2 is finite and its order divides the actual finite Galois degree. -/
theorem originalClassesModOutside_finiteGalois_second_card_dvd :
    Finite (groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2) ∣
        Module.finrank K L := by
  let e := (originalClassesModOutsideH2Iso K L S hS hu).toLinearEquiv.toEquiv
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd K L
  haveI := hf
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e]
  exact hd

end
end Dubon2026
