import Dubon2026.IdeleClassHerbrandFromLocal
import Dubon2026.SupportedUnrestrictedHilbert90

/-! # The original idele-class ratio after discharging unrestricted Hilbert90

The actual original local-stabilizer H1 groups now vanish by the proved
faithful completion-field action and existing Hilbert90. The final
original global formula therefore retains only local H2 orders and
outside-support integer-unit vanishing, alongside the original class
surjection. This reduces DUB-17's remaining norm-index assumptions.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Original idele-class finiteness and its degree ratio follow from the actual local H2 orders and outside-support vanishing; unrestricted H1 is fully discharged. -/
theorem original_ideleClass_herbrand_of_local_second
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    (hsecond : letI := IsCyclic.commGroup (α := Gal(L/K))
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
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
  exact original_ideleClass_herbrand_of_local K L S hS hsurj
    (fun ω => ⟨supportedUnrestrictedOrbitPoint_first_cohomology_zero K L S hS ω, hsecond ω⟩)
    houtside

end
end Dubon2026
