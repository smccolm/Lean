import Dubon2026.SupportedIdeleCohomologyFactors
import Dubon2026.SupportedUnrestrictedOrbitCohomology
import Dubon2026.SupportedOutsideOrbitCohomology

/-! # The original supported-idele factor from actual local stabilizer computations

Original orbit comparisons, outside-support vanishing and the actual
local-factor representation isomorphism derive finite H1/H2 and the
exact original S-unit-place stabilizer factor. Only the displayed local
stabilizer computations remain as inputs to DUB-17's global norm index;
no supported-idele cohomology or global formula is assumed.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Actual local-stabilizer cohomology computes the original supported-idele H1 and H2 completely. -/
theorem original_supportedIdele_cohomology_of_local
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
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1) ∧
      Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2) ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 1) = 1 ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) =
        ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
          Nat.card (MulAction.stabilizer Gal(L/K) ω.out) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  letI := supportedOutsidePlaceAction K L S hS
  have huf1 := supportedUnrestrictedUnit_cohomology_finite K L S hS 1 (fun ω => by
    letI : Subsingleton (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) :=
      ModuleCat.isZero_iff_subsingleton.mp (hlocal ω).1
    exact Finite.of_subsingleton)
  letI : Finite (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 1) := huf1
  letI : Finite (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 2) :=
    supportedUnrestrictedUnit_cohomology_finite K L S hS 2 (fun ω => (hlocal ω).2.1)
  have hu1 : Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 1) = 1 := by
    rw [supportedUnrestrictedUnit_cohomology_card K L S hS 1]
    apply Finset.prod_eq_one
    intro ω _
    letI : Subsingleton (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) :=
      ModuleCat.isZero_iff_subsingleton.mp (hlocal ω).1
    exact Nat.card_unique
  have hu2 : Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 2) =
      ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Nat.card (MulAction.stabilizer Gal(L/K) ω.out) := by
    rw [supportedUnrestrictedUnit_cohomology_card K L S hS 2]
    exact Finset.prod_congr rfl (fun ω _ => (hlocal ω).2.2)
  have ho1 := supportedOutsideUnit_cohomology_zero_of_local K L S hS 1 (by decide)
    (fun ω => (houtside ω).1)
  have ho2 := supportedOutsideUnit_cohomology_zero_of_local K L S hS 2 (by decide)
    (fun ω => (houtside ω).2)
  have hi1 := originalSupportedIdele_cohomology_of_outside_zero K L S hS 1 ho1
  have hi2 := originalSupportedIdele_cohomology_of_outside_zero K L S hS 2 ho2
  exact ⟨hi1.1, hi2.1, hi1.2.trans hu1, hi2.2.trans hu2⟩

end
end Dubon2026
