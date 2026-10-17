import Dubon2026.OriginalUnrestrictedGaloisUnion
import Dubon2026.OriginalUnrestrictedNormalizedClassSystem
import Dubon2026.OriginalKummerNormSupportChoice
import Dubon2026.OriginalSUnitKummerSupportReduction

/-! # Constructing the actual auxiliary Kummer norm field

The auxiliary unrestricted arithmetic union is algebraically closed.
Its actual finite Kummer field has the proved odd-primary degree, so
the existing arithmetic theorem constructs its normalized class system.
The proved support choice and inertia argument then construct the norm
field for the prescribed smaller support. Neither normalization nor
large-support field data are assumptions of this theorem.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

/-- The exact fixed-field conclusion: the prescribed actual norm range
and ramification index one outside the original support. -/
def OriginalPrescribedSupportNormSubfield
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (p : ℕ) : Prop :=
  ∃ (J : Subgroup Gal(L/K)) (hJ : J.Normal),
    letI : J.Normal := hJ
    LinearMap.range (originalIdeleClassNormLinear K (IntermediateField.fixedField J)) =
      LinearMap.range ((p : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap ∧
    ∀ v : HeightOneSpectrum (𝓞 (IntermediateField.fixedField J)),
      originalFinitePrimeBelow K (IntermediateField.fixedField J) v ∉ S →
      (v.asIdeal.under (𝓞 K)).ramificationIdx v.asIdeal = 1

/-- The actual unrestricted arithmetic union is algebraically closed. -/
local instance unrestrictedArithmeticUnionClosed : IsAlgClosed (rationalUnramifiedExtension 0) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  letI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.instIsAlgClosure ℚ
    rw [hAlg] at h
    exact h
  letI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  exact originalUnrestrictedGaloisUnion_isAlgClosed ℚ (AlgebraicClosure ℚ)

variable (F : IntermediateField ℚ (rationalUnramifiedExtension 0))
  [FiniteDimensional ℚ F]

/-- The actual unrestricted ambient field is Galois over each finite base. -/
local instance unrestrictedArithmeticUnionRelativeGalois : IsGalois F (rationalUnramifiedExtension 0) := by
  letI : IsGalois ℚ (rationalUnramifiedExtension 0) := originalUnramifiedGaloisUnion_isGalois 0
  exact IsGalois.tower_top_of_isGalois ℚ F (rationalUnramifiedExtension 0)

/-- An actual finite base containing the odd-prime roots of unity has
a constructed prescribed-support norm field. The auxiliary support,
Kummer degree, class normalization and inertia containment are derived. -/
theorem originalUnrestricted_exists_prescribed_support_norm_field
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ (σ : Gal(F/F)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv F F σ v ∈ S) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧
      let N := OriginalSUnitKummerField F (rationalUnramifiedExtension 0) T p
      letI : FiniteDimensional F N := numberField_sUnit_kummerField_finiteDimensional
        F (rationalUnramifiedExtension 0) T T.finite_toSet p (Fact.out : p.Prime).pos
        ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩
      letI : NumberField N := NumberField.of_module_finite F N
      letI : IsGalois F N := originalKummerRadicalField_isGalois p _
      OriginalPrescribedSupportNormSubfield F N S hS p := by
  have hp : p.Prime := Fact.out
  obtain ⟨T, hST, hT, hClasses, hBase, hAway⟩ :=
    original_exists_kummer_norm_support F p hp.ne_zero S
  refine ⟨T, hST, ?_⟩
  let N := OriginalSUnitKummerField F (rationalUnramifiedExtension 0) T p
  letI : FiniteDimensional F N := numberField_sUnit_kummerField_finiteDimensional
    F (rationalUnramifiedExtension 0) T T.finite_toSet p hp.pos
    ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  letI : NumberField N := NumberField.of_module_finite F N
  letI : IsGalois F N := originalKummerRadicalField_isGalois p _
  have hDegree : Module.finrank F N = p ^ (Fintype.card (InfinitePlace F) + T.card) := by
    simpa only [Set.ncard_coe_finset] using
      numberField_sUnit_kummerField_finrank F (rationalUnramifiedExtension 0)
        T T.finite_toSet p hp.pos ζ hζ
  have hs := originalUnrestricted_finite_normalized_class_system F N p _ hp hp2 hDegree
  exact originalSUnitKummer_exists_prescribed_support_norm_field
    F (rationalUnramifiedExtension 0) p ζ hζ S T hST hS hT hClasses hBase hAway hs

end
end Dubon2026
