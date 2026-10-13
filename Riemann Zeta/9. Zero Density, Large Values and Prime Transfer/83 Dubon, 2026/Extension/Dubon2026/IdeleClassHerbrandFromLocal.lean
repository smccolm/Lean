import Dubon2026.SupportedIdeleHerbrandFromLocal
import Dubon2026.IdeleClassHerbrandFromSupported

/-! # The original idele-class Herbrand formula from the actual local factors

The original supported-idele factor is now derived from the original
local stabilizer modules and combined with the proved S-unit formula
through the actual original short exact sequence. The remaining inputs
are the displayed local computations and actual class surjectivity;
global cohomology finiteness and its orbit factor are discharged.
This is the norm-index lower-bound dependency serving DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual local-stabilizer computations and original class surjection imply finite original idele-class cohomology and its group-order Herbrand ratio. -/
theorem original_ideleClass_herbrand_of_local
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (hlocal : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Limits.IsZero (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) ∧
        Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out))
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
  have hi := original_supportedIdele_cohomology_of_local K L S hS hlocal houtside
  letI : Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1) := hi.1
  letI : Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2) := hi.2.1
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  apply original_ideleClass_herbrand_of_supported K L S hS σ hgen hsurj
  rw [hi.2.2.1, one_mul]
  exact hi.2.2.2

end
end Dubon2026
