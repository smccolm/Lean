import Dubon2026.SupportedOrbitUnitFieldComparison

/-! # Hilbert90 for the actual unrestricted idele stabilizers

The original faithful completion-field action, original coefficient
isomorphism and existing fixed-field Hilbert90 theorem prove local H1
vanishing for every actual orbit representative. The actual finite-orbit
cohomology equivalence then kills the original unrestricted idele H1.
This discharges the local H1 hypotheses in DUB-17's global norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance] Units.mulDistribMulActionRight
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Existing Hilbert90 vanishes on each exact original unrestricted local-stabilizer unit coefficient. -/
theorem supportedUnrestrictedOrbitPoint_first_cohomology_zero :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      Limits.IsZero (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  let H := MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)
  let F := supportedUnrestrictedCompletion L S ω.out
  letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
  letI : FaithfulSMul H F := supportedUnrestrictedOrbitField_faithful K L S hS ω
  have hz := faithfulFieldUnit_first_cohomology_zero H F
  exact Limits.IsZero.of_iso hz
    ((groupCohomology.functor ℤ H 1).mapIso (supportedUnrestrictedOrbitUnitFieldIso K L S hS ω))

/-- Original H1 of the entire actual unrestricted idele factor is zero, with no local vanishing hypotheses. -/
theorem supportedUnrestrictedUnit_first_cohomology_zero :
    Limits.IsZero (groupCohomology (supportedUnrestrictedUnitRep K L S hS) 1) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  letI (ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S)) :
      Subsingleton (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 1) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (supportedUnrestrictedOrbitPoint_first_cohomology_zero K L S hS ω)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact Function.Injective.subsingleton (supportedUnrestrictedOrbitCohomologyEquiv K L S hS 1).injective

end
end Dubon2026
