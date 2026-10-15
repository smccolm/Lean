import Dubon2026.ArithmeticSUnitRepresentation
import Dubon2026.ArithmeticExceptionalSUnitSupport
import Dubon2026.ContinuousCohomologyRestriction
import Dubon2026.ArithmeticSUnitFiniteFieldCoefficients

/-! # The actual finite S-unit coefficient inclusion

The source finite S-unit coefficient maps into the arithmetic integral-closure
units through the original field embedding. Its action is the actual restriction
of the original arithmetic Galois action. This is the coefficient morphism for
continuous finite-stage H2 inflation.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

private def localizedUnitMap (K L Γ : Type) [Field K] [Field L] [Field Γ]
    [NumberField K] [NumberField L] [Algebra K L] [Algebra K Γ]
    (a : 𝓞 K) (ha : a ≠ 0) (j : L →ₐ[K] Γ) :
    (originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
      (originalIntegerMap_ne_zero (L := L) a ha))ˣ →*
      (integralClosure (originalLocalizedIntegers K a ha) Γ)ˣ := by
  let R := originalLocalizedIntegers K a ha
  let S := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
    (originalIntegerMap_ne_zero (L := L) a ha)
  letI : Algebra R S := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsIntegralClosure S R L := (canonicalLocalizedIntegerAlgebra_data (L := L) a ha).2.1
  let e := IsIntegralClosure.equiv R S L (integralClosure R L)
  let jR : L →ₐ[R] Γ := { j.toRingHom with commutes' := fun r => j.commutes r.val }
  exact (Units.map jR.mapIntegralClosure.toMonoidHom).comp (Units.map e.toMonoidHom)

private theorem localizedUnitMap_coe (K L Γ : Type) [Field K] [Field L] [Field Γ]
    [NumberField K] [NumberField L] [Algebra K L] [Algebra K Γ]
    (a : 𝓞 K) (ha : a ≠ 0) (j : L →ₐ[K] Γ)
    (u : (originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
      (originalIntegerMap_ne_zero (L := L) a ha))ˣ) :
    (localizedUnitMap K L Γ a ha j u).val.val = j u.val.val := by
  let R := originalLocalizedIntegers K a ha
  let S := originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
    (originalIntegerMap_ne_zero (L := L) a ha)
  letI : Algebra R S := (originalLocalizedIntegersMap (L := L) a ha).toRingHom.toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsIntegralClosure S R L := (canonicalLocalizedIntegerAlgebra_data (L := L) a ha).2.1
  exact congrArg j (IsIntegralClosure.algebraMap_equiv R S L (integralClosure R L) u.val)

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))

local instance : NumberField F := NumberField.of_module_finite K F

/-- The exact finite-stage exceptional support of the original integer. -/
abbrev arithmeticSUnitFiniteStageSupport :=
  originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)

/-- The original finite-stage S-unit representation, with its actual Galois action. -/
def arithmeticSUnitFiniteStageRep : Rep ℤ Gal(F/K) :=
  sUnitOriginalRep K F (arithmeticSUnitFiniteStageSupport K Ω a ha F)
    (originalExceptionalIntegerSupport_galoisStable F K a ha)

/-- The source S-unit coefficient embeds through the actual original field inclusion. -/
def arithmeticSUnitFiniteStageUnitMap :
    (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F →*
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
  (localizedUnitMap K F (originalUnramifiedGaloisUnion (Ω := Ω) a) a ha F.toIntermediateField.val).comp
    (originalLocalizedUnitsEquivSupportedSUnits F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha)).symm.toMonoidHom

/-- The finite-stage coefficient map retains the original ambient field value. -/
theorem arithmeticSUnitFiniteStageUnitMap_coe
    (u : (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
      Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F) :
    (arithmeticSUnitFiniteStageUnitMap K Ω a ha F u).val.val =
      algebraMap F (originalUnramifiedGaloisUnion (Ω := Ω) a) u.val.val := by
  let e := originalLocalizedUnitsEquivSupportedSUnits F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)
  have he := originalLocalizedUnitsEquivSupportedSUnits_coe F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha) (e.symm u)
  have hv : (e.symm u).val.val = u.val.val := by
    rw [show originalLocalizedUnitsEquivSupportedSUnits F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha) (e.symm u) = u from e.apply_symm_apply u] at he
    exact he.symm
  exact (localizedUnitMap_coe K F (originalUnramifiedGaloisUnion (Ω := Ω) a)
    a ha F.toIntermediateField.val (e.symm u)).trans (congrArg (algebraMap F _) hv)

/-- The finite-stage coefficient map is injective on the original S-units. -/
theorem arithmeticSUnitFiniteStageUnitMap_injective :
    Function.Injective (arithmeticSUnitFiniteStageUnitMap K Ω a ha F) := by
  intro u v h
  have he := congrArg (fun x : (OriginalArithmeticSUnitRing K Ω a ha)ˣ => x.val.val) h
  have he' := (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F u).symm.trans
    (he.trans (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F v))
  apply Subtype.ext
  apply Units.ext
  exact F.toIntermediateField.val.injective he'

/-- The actual finite-stage image consists exactly of the arithmetic S-units whose original field values belong to that stage. -/
theorem arithmeticSUnitFiniteStageUnitMap_mem_range_iff
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    u ∈ (arithmeticSUnitFiniteStageUnitMap K Ω a ha F).range ↔
      u.val.val ∈ F.toIntermediateField := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [arithmeticSUnitFiniteStageUnitMap_coe]
    exact v.val.val.property
  · intro hu
    obtain ⟨v, hv⟩ := originalArithmeticSUnit_supportedPreimage_at_finiteField K Ω a ha F u hu
    refine ⟨v, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F v).trans hv

/-- The exact finite-stage coefficient map intertwines actual Galois restriction and the arithmetic action. -/
def arithmeticSUnitFiniteStageInclusion :
    restrictedCoefficientRep (arithmeticSUnitFiniteStageRep K Ω a ha F)
      (AlgEquiv.restrictNormalHom F :
        Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(F/K)) ⟶
      originalArithmeticSUnitRepresentation K Ω a ha :=
  Rep.ofHom {
    toLinearMap := (arithmeticSUnitFiniteStageUnitMap K Ω a ha F).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      apply Subtype.ext
      change (arithmeticSUnitFiniteStageUnitMap K Ω a ha F
        ((arithmeticSUnitFiniteStageRep K Ω a ha F).ρ (AlgEquiv.restrictNormalHom F g) x).toMul).val.val =
          g (arithmeticSUnitFiniteStageUnitMap K Ω a ha F x.toMul).val.val
      rw [arithmeticSUnitFiniteStageUnitMap_coe, arithmeticSUnitFiniteStageUnitMap_coe]
      exact AlgEquiv.restrictNormal_commutes g F x.toMul.val.val }

/-- The original coefficient morphism evaluates as the literal constructed S-unit inclusion. -/
theorem arithmeticSUnitFiniteStageInclusion_apply (x : arithmeticSUnitFiniteStageRep K Ω a ha F) :
    (arithmeticSUnitFiniteStageInclusion K Ω a ha F).hom x =
      Additive.ofMul (arithmeticSUnitFiniteStageUnitMap K Ω a ha F x.toMul) := rfl

end
end Dubon2026
