import Dubon2026.IdeleClassHerbrandFromArchimedeanSecond
import Dubon2026.SupportedArchimedeanSecondCohomology

/-! # Original idele-class ratio after all unrestricted local computations

Original faithful-action Hilbert90, finite-place local H2 and actual
archimedean stabilizer H2 are all consumed. Only the actual outside-support
integer-unit vanishing and actual class surjection remain as hypotheses.
This is the explicit remaining local dependency of DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Original idele-class finiteness and its degree ratio follow from actual outside-support integer-unit vanishing and the actual class surjection; every unrestricted local cohomology input is discharged. -/
theorem original_ideleClass_herbrand_of_outside
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (houtside : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := supportedOutsidePlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 1) ∧
        Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) 2)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  exact original_ideleClass_herbrand_of_archimedean_second K L S hS hsurj
    (supportedArchimedeanOrbitPoint_second_cohomology_order K L S hS) houtside

end
end Dubon2026
