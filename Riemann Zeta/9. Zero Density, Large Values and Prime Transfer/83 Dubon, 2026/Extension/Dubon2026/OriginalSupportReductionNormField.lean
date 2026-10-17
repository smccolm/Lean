import Dubon2026.OriginalOutsideClassAntitone
import Dubon2026.OriginalPrescribedSupportNormField

/-! # Reducing a large-support norm field to the prescribed support

The proved antitone outside-unit image makes the large-support norm
subgroup lie in the required power-plus-outside subgroup. The constructed
norm correspondence then produces the exact smaller-support field.
This removes the submodule-containment premise before DUB-17's Kummer
stage placement and invariant norm-root argument.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
  (S T : Finset (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(K/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ T)

/-- The large-support norm equality constructs a normal field with the
exact prescribed power-plus-outside norm subgroup and no ramification
outside the smaller support. -/
theorem originalFullClass_exists_reduced_support_norm_field
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (hsys : OriginalFiniteNormalizedClassSystem K L) (hST : S ⊆ T)
    (hNorm : LinearMap.range (originalIdeleClassNormLinear K L) =
      LinearMap.range ((p : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K T hT).hom.toLinearMap) :
    ∃ (H : Subgroup Gal(L/K)) (hH : H.Normal),
      letI : H.Normal := hH
      LinearMap.range (originalIdeleClassNormLinear K (IntermediateField.fixedField H)) =
        LinearMap.range ((p : ℤ) • (LinearMap.id :
          originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
        LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap ∧
      ∀ q : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)),
        originalFinitePrimeBelow K (IntermediateField.fixedField H) q ∉ S →
        (q.asIdeal.under (𝓞 K)).ramificationIdx q.asIdeal = 1 := by
  apply originalFullClass_exists_prescribed_support_norm_field_of_base_support K L S hS p hG hsys
  · rw [hNorm]
    exact sup_le_sup le_rfl (originalOutsideIdeleClass_range_antitone K S T hS hT hST)
  · intro z
    exact Submodule.mem_sup_right ⟨z, rfl⟩

end
end Dubon2026
