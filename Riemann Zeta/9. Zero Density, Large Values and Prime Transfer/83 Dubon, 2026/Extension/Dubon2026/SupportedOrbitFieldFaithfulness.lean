import Dubon2026.SupportedUnrestrictedFieldTransports
import Dubon2026.SupportedUnrestrictedOrbitCohomology

/-! # Faithful original stabilizer actions on unrestricted completion fields

Every original orbit stabilizer acts by the original completed field
maps. Equality on the actual completion implies equality on the embedded
original global field, hence equality of the original automorphisms.
This discharges faithfulness for DUB-17's local Hilbert90 application.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original orbit stabilizer acts on the actual original completion at its representative. -/
@[reducible]
def supportedUnrestrictedOrbitFieldAction :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      MulSemiringAction
        (MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω))
        (supportedUnrestrictedCompletion L S ω.out) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  exact {
    smul σ x := supportedUnrestrictedFieldTransport K L S hS σ.val ω.out ω.out
      (congrArg Subtype.val σ.property) x
    one_smul x := supportedUnrestrictedFieldTransport_one K L S hS ω.out x
    mul_smul σ τ x := supportedUnrestrictedFieldTransport_mul K L S hS σ.val τ.val
      ω.out ω.out ω.out (congrArg Subtype.val τ.property) (congrArg Subtype.val σ.property)
      (congrArg Subtype.val (σ * τ).property) x
    smul_zero σ := map_zero _
    smul_add σ := map_add _
    smul_one σ := map_one _
    smul_mul σ := map_mul _ }

/-- The actual original stabilizer action on each original completion field is faithful. -/
theorem supportedUnrestrictedOrbitField_faithful :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
      FaithfulSMul
        (MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω))
        (supportedUnrestrictedCompletion L S ω.out) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
  refine ⟨?_⟩
  intro σ τ he
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (supportedUnrestrictedCompletion L S ω.out)).injective
  have h := he (algebraMap L (supportedUnrestrictedCompletion L S ω.out) x)
  change supportedUnrestrictedFieldTransport K L S hS σ.val ω.out ω.out _
      (algebraMap L (supportedUnrestrictedCompletion L S ω.out) x) =
    supportedUnrestrictedFieldTransport K L S hS τ.val ω.out ω.out _
      (algebraMap L (supportedUnrestrictedCompletion L S ω.out) x) at h
  simpa only [supportedUnrestrictedFieldTransport_algebraMap] using h

end
end Dubon2026
