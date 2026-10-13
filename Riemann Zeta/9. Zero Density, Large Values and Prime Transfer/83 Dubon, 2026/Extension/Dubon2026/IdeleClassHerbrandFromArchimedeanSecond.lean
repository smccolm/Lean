import Dubon2026.IdeleClassHerbrandFromLocalSecond
import Dubon2026.SupportedFiniteOrbitSecondCohomology

/-! # Original idele-class ratio with finite-place H2 discharged

The exact finite-place orbit H2 computation is now consumed, in addition
to original unrestricted Hilbert90. Only archimedean H2, outside-support
integer-unit vanishing and the actual class surjection remain as inputs.
This is the next explicit reduction in DUB-17's global norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Original idele-class finiteness and its degree ratio retain only actual archimedean H2 and outside-support vanishing; all unrestricted H1 and finite-place H2 inputs are discharged. -/
theorem original_ideleClass_herbrand_of_archimedean_second
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (harch : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        ω.out.isLeft →
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
  apply original_ideleClass_herbrand_of_local_second K L S hS hsurj ?_ houtside
  intro ω
  by_cases hf : ω.out.isRight
  · exact supportedFiniteOrbitPoint_second_cohomology_order K L S hS ω hf
  · apply harch ω
    cases hp : ω.out <;> simp_all

end
end Dubon2026
