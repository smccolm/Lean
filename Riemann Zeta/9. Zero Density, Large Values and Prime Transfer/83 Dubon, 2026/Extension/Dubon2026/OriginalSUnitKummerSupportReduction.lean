import Dubon2026.OriginalSupportReductionNormField
import Dubon2026.OriginalSUnitKummerNormField

/-! # The actual S-unit Kummer field yields the prescribed-support norm field

The original radical field supplies its Galois group, exponent, degree
and large-support norm equality. The proved support reduction then
constructs the desired fixed field. Only normalization of that actual
Kummer stage remains explicit before DUB-17's arithmetic placement step.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The literal large S-unit radical field constructs a normal subfield
with exactly the prescribed smaller-support norm subgroup and index one
outside that support. Its class normalization is the explicit remaining input. -/
theorem originalSUnitKummer_exists_prescribed_support_norm_field
    (p : ℕ) [Fact p.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ T)
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (hT : ∀ (σ : Gal(K/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ T)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K T))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → (p : 𝓞 K) ∉ v.asIdeal) :
    let N := OriginalSUnitKummerField K Ω T p
    letI : FiniteDimensional K N := numberField_sUnit_kummerField_finiteDimensional
      K Ω T T.finite_toSet p (Fact.out : p.Prime).pos
      ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩
    letI : NumberField N := NumberField.of_module_finite K N
    letI : IsGalois K N := originalKummerRadicalField_isGalois p _
    OriginalFiniteNormalizedClassSystem K N →
      ∃ (H : Subgroup Gal(N/K)) (hH : H.Normal),
        letI : H.Normal := hH
        LinearMap.range (originalIdeleClassNormLinear K (IntermediateField.fixedField H)) =
          LinearMap.range ((p : ℤ) • (LinearMap.id :
            originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
          LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap ∧
        ∀ q : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)),
          originalFinitePrimeBelow K (IntermediateField.fixedField H) q ∉ S →
          (q.asIdeal.under (𝓞 K)).ramificationIdx q.asIdeal = 1 := by
  have hp : p.Prime := Fact.out
  have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  let N := OriginalSUnitKummerField K Ω T p
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω T T.finite_toSet p hp.pos hroot
  letI : NumberField N := NumberField.of_module_finite K N
  letI : IsGalois K N := originalKummerRadicalField_isGalois p _
  letI : IsMulCommutative Gal(N/K) := originalKummerRadicalField_galois_commutative p hroot _
  dsimp only
  intro hsys
  have hDegree : Module.finrank K N = p ^ (Fintype.card (InfinitePlace K) + T.card) := by
    simpa only [Set.ncard_coe_finset] using
      numberField_sUnit_kummerField_finrank K Ω T T.finite_toSet p hp.pos ζ hζ
  have hG : IsPGroup p Gal(N/K) :=
    IsPGroup.of_card ((IsGalois.card_aut_eq_finrank K N).trans hDegree)
  exact originalFullClass_exists_reduced_support_norm_field K N S T hS hT p hG hsys hST
    (originalSUnitKummer_normRange_eq_power_sup_outside K Ω p ζ hζ T hT hClasses hBase hAway hsys)

end
end Dubon2026
