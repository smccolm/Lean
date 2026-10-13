import Dubon2026.OriginalIdeleClassSubgroupCohomology
import Mathlib.RepresentationTheory.Invariants

/-! # Actual fixed-field classes are the original normal invariant coefficients

Proved original class descent and Galois equivariance identify the normal
quotient coefficients with actual classes over the fixed field. This
discharges the coefficient identification needed for finite-stage
inflation-restriction in DUB-17's global invariant and duality chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Actual fixed-field class inclusion into the original quotient invariant representation. -/
def originalIdeleClassNormalInvariantInclusion :
    Rep.res (IsGalois.normalAutEquivQuotient S).toMonoidHom
        (originalIdeleClassRep K (IntermediateField.fixedField S)) ⟶
      (originalIdeleClassRep K L).quotientToInvariants S := by
  let F := IntermediateField.fixedField S
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup S
  refine Rep.ofHom ⟨
    ((originalIdeleClassBaseChangeMap F L).toAdditive.toIntLinearMap).codRestrict
      _ (fun u s => ?_), fun q => ?_⟩
  · exact congrArg Additive.ofMul
      (originalIdeleClassBaseChangeMap_fixed F L
        (IntermediateField.subgroupEquivAlgEquiv S s) u.toMul)
  · apply LinearMap.ext
    intro u
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      exact congrArg Additive.ofMul
        (originalIdeleClassBaseChangeMap_restrictNormal K F L g u.toMul).symm

/-- Proved original class descent gives bijectivity of the actual normal invariant inclusion. -/
theorem originalIdeleClassNormalInvariantInclusion_bijective :
    Function.Bijective (originalIdeleClassNormalInvariantInclusion S).hom := by
  let F := IntermediateField.fixedField S
  constructor
  · intro u v huv
    apply Additive.toMul.injective
    apply originalIdeleClassBaseChangeMap_injective F L
    exact congrArg (fun z => Additive.toMul z.val) huv
  · intro x
    obtain ⟨c, hc⟩ := originalIdeleClassBaseChangeMap_surjective_fixed F L x.val.toMul
      (fun σ => by
        obtain ⟨s, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv S).surjective σ
        exact congrArg Additive.toMul (x.property s))
    exact ⟨Additive.ofMul c, Subtype.ext (congrArg Additive.ofMul hc)⟩

/-- The actual normal quotient invariant coefficient representation is the fixed-field one. -/
def originalIdeleClassNormalInvariantCoefficientIso :
    Rep.res (IsGalois.normalAutEquivQuotient S).toMonoidHom
        (originalIdeleClassRep K (IntermediateField.fixedField S)) ≅
      (originalIdeleClassRep K L).quotientToInvariants S := by
  haveI : Mono (originalIdeleClassNormalInvariantInclusion S) :=
    (Rep.mono_iff_injective _).mpr (originalIdeleClassNormalInvariantInclusion_bijective S).1
  haveI : Epi (originalIdeleClassNormalInvariantInclusion S) :=
    (Rep.epi_iff_surjective _).mpr (originalIdeleClassNormalInvariantInclusion_bijective S).2
  haveI : IsIso (originalIdeleClassNormalInvariantInclusion S) := isIso_of_mono_of_epi _
  exact asIso (originalIdeleClassNormalInvariantInclusion S)

/-- Cohomology of the actual normal invariants equals original fixed-field class cohomology. -/
def originalIdeleClassNormalInvariantCohomologyIso (n : ℕ) :
    groupCohomology (originalIdeleClassRep K (IntermediateField.fixedField S)) n ≅
      groupCohomology ((originalIdeleClassRep K L).quotientToInvariants S) n :=
  originalCohomologyReindex _ (IsGalois.normalAutEquivQuotient S) n ≪≫
    (groupCohomology.functor ℤ (Gal(L/K) ⧸ S) n).mapIso
      (originalIdeleClassNormalInvariantCoefficientIso S)

end
end Dubon2026
