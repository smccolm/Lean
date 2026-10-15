import Dubon2026.OriginalClassQuotientBaseInvariants
import Dubon2026.OriginalIdeleClassNormalInvariants

/-! # Original fixed-field class quotients are the normal invariant coefficients

The original outside-unit quotient and its literal base-change map are
retained under the normal invariant action. Existing invariant descent
supplies bijectivity. This identifies the finite quotient coefficients
needed for the H2 normalization in DUB-17's arithmetic P-class formation,
before Ext duality and reverse arithmetic localization inclusion.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (H : Subgroup Gal(L/K)) [H.Normal]


/-- The actual fixed field of the normal subgroup is Galois over the original base. -/
local instance normalClassFixedFieldGalois : IsGalois K (IntermediateField.fixedField H) :=
  IsGalois.of_fixedField_normal_subgroup H

variable (S : Finset (HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal((IntermediateField.fixedField H)/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K (IntermediateField.fixedField H) σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow (IntermediateField.fixedField H) L w ∈ S)

include hS in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] [H.Normal] in
/-- The fixed-field support is unchanged on restricting to automorphisms over itself. -/
theorem originalNormalClassBaseSupport (σ : Gal((IntermediateField.fixedField H)/(IntermediateField.fixedField H))) (v : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H))) :
    v ∈ S ↔ numberFieldGaloisPlaceEquiv (IntermediateField.fixedField H) (IntermediateField.fixedField H) σ v ∈ S :=
  hS (σ.restrictScalars K) v

include hT in
omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] [H.Normal] in
/-- The original upper support is unchanged on restricting to the actual fixed field. -/
theorem originalNormalClassUpperSupport (σ : Gal(L/(IntermediateField.fixedField H))) (v : HeightOneSpectrum (𝓞 L)) :
    v ∈ T ↔ numberFieldGaloisPlaceEquiv (IntermediateField.fixedField H) L σ v ∈ T :=
  hT (σ.restrictScalars K) v

/-- Original fixed-field class quotient inclusion into the literal normal invariants. -/
def originalClassQuotientNormalInvariantInclusion :
    Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (originalIdeleClassesModOutsideRep K (IntermediateField.fixedField H) S hS) ⟶
      (originalIdeleClassesModOutsideRep K L T hT).quotientToInvariants H := by
  let φ := originalClassesModOutsideBaseChangeRepHom K (IntermediateField.fixedField H) L S T hS hT hST
  let j := originalClassesModOutsideBaseInvariant (IntermediateField.fixedField H) L S T
    (originalNormalClassBaseSupport K L H S hS)
    (originalNormalClassUpperSupport K L H T hT) hST
  refine Rep.ofHom ⟨φ.hom.toLinearMap.codRestrict _ (fun x s => ?_), fun q => ?_⟩
  · exact (j x).property (IntermediateField.subgroupEquivAlgEquiv H s)
  · apply LinearMap.ext
    intro x
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      exact Rep.hom_comm_apply φ g x

/-- Original quotient invariant descent makes the actual normal invariant inclusion bijective. -/
theorem originalClassQuotientNormalInvariantInclusion_bijective
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Bijective (originalClassQuotientNormalInvariantInclusion K L H S T hS hT hST).hom := by
  have hj := originalClassesModOutsideBaseInvariant_bijective (IntermediateField.fixedField H) L S T
    (originalNormalClassBaseSupport K L H S hS)
    (originalNormalClassUpperSupport K L H T hT) hST hu
  constructor
  · intro x y h
    apply hj.1
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact he
  · intro x
    have hx : ∀ σ : Gal(L/(IntermediateField.fixedField H)), (originalIdeleClassesModOutsideRep (IntermediateField.fixedField H) L T
        (originalNormalClassUpperSupport K L H T hT)).ρ σ x.val = x.val := by
      intro σ
      obtain ⟨s, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv H).surjective σ
      exact x.property s
    obtain ⟨y, hy⟩ := hj.2 ⟨x.val, hx⟩
    have he := congrArg Subtype.val hy
    exact ⟨y, Subtype.ext he⟩

/-- Actual fixed-field quotient classes give the original normal invariant representation. -/
def originalClassQuotientNormalInvariantCoefficientIso
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (originalIdeleClassesModOutsideRep K (IntermediateField.fixedField H) S hS) ≅
      (originalIdeleClassesModOutsideRep K L T hT).quotientToInvariants H := by
  let φ := originalClassQuotientNormalInvariantInclusion K L H S T hS hT hST
  have hφ := originalClassQuotientNormalInvariantInclusion_bijective K L H S T hS hT hST hu
  haveI : Mono φ := (Rep.mono_iff_injective _).mpr hφ.1
  haveI : Epi φ := (Rep.epi_iff_surjective _).mpr hφ.2
  haveI : IsIso φ := isIso_of_mono_of_epi _
  exact asIso φ

/-- The actual fixed-field class quotient H2 equals H2 of the original normal invariant coefficient. -/
def originalClassQuotientNormalInvariantH2Iso
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    groupCohomology (originalIdeleClassesModOutsideRep K (IntermediateField.fixedField H) S hS) 2 ≅
      groupCohomology ((originalIdeleClassesModOutsideRep K L T hT).quotientToInvariants H) 2 :=
  originalCohomologyReindex _ (IsGalois.normalAutEquivQuotient H) 2 ≪≫
    (groupCohomology.functor ℤ (Gal(L/K) ⧸ H) 2).mapIso
      (originalClassQuotientNormalInvariantCoefficientIso K L H S T hS hT hST hu)

end
end Dubon2026
