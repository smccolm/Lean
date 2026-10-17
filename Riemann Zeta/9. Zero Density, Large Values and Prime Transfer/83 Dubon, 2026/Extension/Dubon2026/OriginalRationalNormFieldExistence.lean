import Dubon2026.OriginalUnrestrictedNumberFieldRealization
import Dubon2026.OriginalDegreeOneNormFieldTower
import Dubon2026.OriginalNormFieldBaseDescent
import Dubon2026.UnramifiedNormalClosure

/-! # An actual norm field over the original number field

Construct the prescribed-support Kummer norm field in an isomorphic
finite base inside the unrestricted arithmetic union. Its literal field
norm descends to the original base. Degree-one ramification and the
existing unramified tower preserve the original exceptional support.
The resulting containment is exactly the input needed for DUB-17's
invariant norm roots, without a normalized-system or norm-field premise.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField unrestrictedArithmeticUnionClosed
  unrestrictedArithmeticUnionRelativeGalois

/-- The precise finite-extension input to invariant norm roots: literal
power-plus-outside norm containment and the original relative ramification.
This proposition is a specification; the construction is proved below. -/
def OriginalRationalPowerNormField (K : Type) [Field K] [NumberField K]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) : Prop :=
  let S := originalExceptionalIntegerSupport K (algebraMap (𝓞 ℚ) (𝓞 K) a)
    (originalIntegerMap_ne_zero (L := K) a ha)
  let hS := fun (σ : Gal(K/K)) v =>
    originalExceptionalIntegerSupport_galoisStable K ℚ a ha (σ.restrictScalars ℚ) v
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
    (_ : FiniteDimensional K L) (_ : IsGalois K L),
    (originalIdeleClassNormLinear K L).range ≤
      LinearMap.range ((p : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap ∧
    ∀ w : HeightOneSpectrum (𝓞 L),
      algebraMap (𝓞 K) (𝓞 L) (algebraMap (𝓞 ℚ) (𝓞 K) a) ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1

/-- The constructed normal fixed subfield supplies the actual finite
norm extension, retaining its literal relative ramification. -/
theorem originalRationalPowerNormField_of_prescribed_subfield
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ)
    (h : OriginalPrescribedSupportNormSubfield K L
      (originalExceptionalIntegerSupport K (algebraMap (𝓞 ℚ) (𝓞 K) a)
        (originalIntegerMap_ne_zero (L := K) a ha))
      (fun σ v => originalExceptionalIntegerSupport_galoisStable K ℚ a ha
        (σ.restrictScalars ℚ) v) p) :
    OriginalRationalPowerNormField K a ha p := by
  obtain ⟨J, hJ, hn, hu⟩ := h
  letI : J.Normal := hJ
  letI : IsGalois K (IntermediateField.fixedField J) := IsGalois.of_fixedField_normal_subgroup J
  refine ⟨IntermediateField.fixedField J, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hn.le, ?_⟩
  intro w hw
  apply hu w
  rw [mem_originalExceptionalIntegerSupport]
  exact hw

/-- Literal norm descent and the unramified tower return a norm field
from a degree-one realization to the original number field. -/
theorem originalRationalPowerNormField_of_degreeOne
    (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] [IsScalarTower ℚ K F] [FiniteDimensional K F] [IsGalois K F]
    (hKF : Module.finrank K F = 1) (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ)
    (h : OriginalRationalPowerNormField F a ha p) :
    OriginalRationalPowerNormField K a ha p := by
  let S := originalExceptionalIntegerSupport K (algebraMap (𝓞 ℚ) (𝓞 K) a)
    (originalIntegerMap_ne_zero (L := K) a ha)
  let T := originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)
  have hS (σ : Gal(K/K)) v : v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S :=
    originalExceptionalIntegerSupport_galoisStable K ℚ a ha (σ.restrictScalars ℚ) v
  have hT (σ : Gal(F/K)) v : v ∈ T ↔ numberFieldGaloisPlaceEquiv K F σ v ∈ T :=
    originalExceptionalIntegerSupport_galoisStable F ℚ a ha (σ.restrictScalars ℚ) v
  have hTF (σ : Gal(F/F)) v : v ∈ T ↔ numberFieldGaloisPlaceEquiv F F σ v ∈ T :=
    originalExceptionalIntegerSupport_galoisStable F ℚ a ha (σ.restrictScalars ℚ) v
  have hST (w : HeightOneSpectrum (𝓞 F)) : w ∈ T ↔ originalFinitePrimeBelow K F w ∈ S := by
    rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
    change algebraMap (𝓞 ℚ) (𝓞 F) a ∈ w.asIdeal ↔
      algebraMap (𝓞 K) (𝓞 F) (algebraMap (𝓞 ℚ) (𝓞 K) a) ∈ w.asIdeal
    rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 K) (𝓞 F)]
  obtain ⟨L, hL, hNL, hFL, hFinite, hGal, hn, hu⟩ := h
  letI := hL
  letI := hNL
  letI := hFL
  letI := hFinite
  letI := hGal
  letI : Algebra K L := Algebra.compHom L (algebraMap K F)
  letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K L := Module.Finite.trans F L
  letI : IsGalois K L := originalDegreeOne_tower_isGalois K F hKF L
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact originalNormField_containment_descends_base K F L S T hS hT hTF hST p hn
  · apply numberField_unramified_tower (K := K) (L := F) (M := L)
      (algebraMap (𝓞 ℚ) (𝓞 K) a)
    · intro w _
      exact originalDegreeOne_ramification_one K F hKF w
    · intro w hw
      apply hu w
      simpa only [← IsScalarTower.algebraMap_apply] using hw

/-- The actual original number field containing an odd-prime primitive
root has a constructed finite Galois norm field with the required
ramification. All auxiliary field, support and normalization data are derived. -/
theorem originalNumberField_exists_rational_power_norm_field
    (K : Type) [Field K] [NumberField K]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    OriginalRationalPowerNormField K a ha p := by
  obtain ⟨F, hF, ⟨e⟩⟩ := originalNumberField_exists_unrestricted_arithmetic_realization K
  letI : FiniteDimensional ℚ F := hF
  letI : Algebra K F := e.toRingHom.toAlgebra
  letI : IsScalarTower ℚ K F := IsScalarTower.of_algHom e.toAlgHom
  let ek : K ≃ₐ[K] F := { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : FiniteDimensional K F := Module.Finite.of_surjective ek.toLinearMap ek.surjective
  letI : IsGalois K F := IsGalois.of_algEquiv ek
  have hKF : Module.finrank K F = 1 := Module.finrank_of_bijective_algebraMap ek.bijective
  let T := originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)
  have hTF (σ : Gal(F/F)) v : v ∈ T ↔ numberFieldGaloisPlaceEquiv F F σ v ∈ T :=
    originalExceptionalIntegerSupport_galoisStable F ℚ a ha (σ.restrictScalars ℚ) v
  have hroot : IsPrimitiveRoot (e ζ) p := hζ.map_of_injective e.injective
  obtain ⟨U, _hTU, hNormField⟩ :=
    originalUnrestricted_exists_prescribed_support_norm_field F p hp2 (e ζ) hroot T hTF
  let N := OriginalSUnitKummerField F (rationalUnramifiedExtension 0) U p
  letI : FiniteDimensional F N := numberField_sUnit_kummerField_finiteDimensional
    F (rationalUnramifiedExtension 0) U U.finite_toSet p (Fact.out : p.Prime).pos
    ⟨e ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hroot⟩
  letI : NumberField N := NumberField.of_module_finite F N
  letI : IsGalois F N := originalKummerRadicalField_isGalois p _
  exact originalRationalPowerNormField_of_degreeOne K F hKF a ha p
    (originalRationalPowerNormField_of_prescribed_subfield F N a ha p hNormField)

end
end Dubon2026
