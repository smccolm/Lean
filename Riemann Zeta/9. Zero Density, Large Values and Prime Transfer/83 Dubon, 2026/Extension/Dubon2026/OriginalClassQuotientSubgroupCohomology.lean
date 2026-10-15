import Dubon2026.OriginalClassesModOutsideH1
import Dubon2026.OriginalIdeleClassSubgroupCohomology

/-! # Actual class-quotient cohomology on finite Galois subgroups

The underlying original outside-unit quotient is unchanged on passing to
the actual fixed field. Original Galois reindexing therefore transfers the
proved finite H1 vanishing to every subgroup. This is needed to discharge
the open-subgroup H1 class-formation input on DUB-17's duality route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (H : Subgroup Gal(L/K))

include hS in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The original unchanged support is stable under the actual fixed-field Galois action. -/
theorem originalClassQuotient_fixedField_support
    (σ : Gal(L / IntermediateField.fixedField H)) (v : HeightOneSpectrum (𝓞 L)) :
    v ∈ S ↔ numberFieldGaloisPlaceEquiv (IntermediateField.fixedField H) L σ v ∈ S :=
  hS (σ.restrictScalars K) v

/-- Original fixed-field and subgroup actions have the same literal class quotient coefficient. -/
def originalClassQuotientSubgroupCoefficientIso :
    Rep.res (IntermediateField.subgroupEquivAlgEquiv H).toMonoidHom
      (originalIdeleClassesModOutsideRep (IntermediateField.fixedField H) L S
        (originalClassQuotient_fixedField_support K L S hS H)) ≅
      Rep.res H.subtype (originalIdeleClassesModOutsideRep K L S hS) :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (originalIdeleClassesModOutsideRep K L S hS)
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      rfl }

/-- The original fixed-field class-quotient cohomology equals the literal subgroup cohomology. -/
def originalClassQuotientSubgroupCohomologyIso (n : ℕ) :
    groupCohomology (originalIdeleClassesModOutsideRep (IntermediateField.fixedField H) L S
      (originalClassQuotient_fixedField_support K L S hS H)) n ≅
      groupCohomology (Rep.res H.subtype (originalIdeleClassesModOutsideRep K L S hS)) n :=
  originalCohomologyReindex _ (IntermediateField.subgroupEquivAlgEquiv H) n ≪≫
    (groupCohomology.functor ℤ H n).mapIso
      (originalClassQuotientSubgroupCoefficientIso K L S hS H)

/-- Every actual finite Galois subgroup has vanishing original class-quotient H1 at the same unramified support. -/
theorem originalClassQuotientSubgroup_first_zero
    [IsGalois K L]
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalIdeleClassesModOutsideRep K L S hS)) 1) :=
  (originalClassesModOutside_first_zero (IntermediateField.fixedField H) L S
    (originalClassQuotient_fixedField_support K L S hS H) hu).of_iso
      (originalClassQuotientSubgroupCohomologyIso K L S hS H 1).symm

end
end Dubon2026
