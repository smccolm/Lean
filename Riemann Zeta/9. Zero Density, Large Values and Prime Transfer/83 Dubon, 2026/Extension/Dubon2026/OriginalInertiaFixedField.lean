import Dubon2026.OriginalInertiaValuation
import Dubon2026.NumberFieldInertiaRamification
import Dubon2026.OriginalAdicUnitCohomology

/-! # Actual inertia subgroups give totally ramified fixed-field stages

The literal Galois fixed-field equivalence identifies every subgroup of
original inertia with the full inertia and decomposition group above its
fixed field. Pinned ramification cardinality then supplies the exact
ramification input for integral local norm representatives in DUB-17.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : HeightOneSpectrum (𝓞 L)) (S : Subgroup Gal(L/K))
  (hS : S ≤ w.asIdeal.inertia Gal(L/K))

include hS in
omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- Over the literal fixed field of an inertia subgroup, all actual
Galois automorphisms belong to the original prime inertia. -/
theorem originalInertiaFixedField_inertia_top :
    w.asIdeal.inertia Gal(L/IntermediateField.fixedField S) = ⊤ := by
  apply top_unique
  intro τ _
  obtain ⟨σ, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv S).surjective τ
  intro a
  exact (hS σ.property) a

include hS in
omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The actual decomposition group over that same fixed field is full. -/
theorem originalInertiaFixedField_decomposition_top :
    OriginalFiniteDecompositionGroup (IntermediateField.fixedField S) L w = ⊤ := by
  apply top_unique
  intro τ _
  apply originalInertia_fixes_prime (IntermediateField.fixedField S) L w τ
  rw [originalInertiaFixedField_inertia_top w S hS]
  trivial

include hS in
/-- The actual ramification index over the inertia fixed field equals
the full local decomposition order. -/
theorem originalInertiaFixedField_ramification_eq_card
    (v : HeightOneSpectrum (𝓞 (IntermediateField.fixedField S)))
    [w.asIdeal.LiesOver v.asIdeal] :
    v.asIdeal.ramificationIdx w.asIdeal =
      Nat.card (OriginalFiniteDecompositionGroup (IntermediateField.fixedField S) L w) := by
  rw [← numberField_card_inertia_eq_ramificationIdx v w,
    originalInertiaFixedField_inertia_top w S hS,
    originalInertiaFixedField_decomposition_top w S hS]

/-- The original inertia subgroup and the actual full decomposition
group above its fixed field are the same automorphisms. -/
def originalInertiaFixedDecompositionEquiv :
    S ≃* OriginalFiniteDecompositionGroup (IntermediateField.fixedField S) L w :=
  (IntermediateField.subgroupEquivAlgEquiv S).trans
    ((MulEquiv.subgroupCongr (originalInertiaFixedField_decomposition_top w S hS)).trans
      Subgroup.topEquiv).symm

end
end Dubon2026
