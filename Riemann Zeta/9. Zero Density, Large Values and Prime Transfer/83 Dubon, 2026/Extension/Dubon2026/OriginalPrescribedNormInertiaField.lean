import Dubon2026.OriginalInertiaOutsideNormImage
import Dubon2026.OriginalFullClassSpecifiedNormMap
import Dubon2026.OriginalCompletionNormComparisonClosure
import Dubon2026.OriginalNormalizedCompletionNormSystem
import Dubon2026.OriginalPrescribedNormSubfield

/-! # Prescribed actual norm fields contain the required inertia

One source-normalized cocycle supplies both the literal fixed-field norm
correspondence and every completion comparison. The resulting field
contains all inertia outside the prescribed support. This discharges
the inertia-containment obligation in DUB-17's norm-field construction;
placement in the original arithmetic stage remains a separate step.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField IsMulCommutative
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

include hT hST in
/-- A prescribed submodule containing the literal full norm range and
base outside-unit classes is the norm range of a normal fixed field
whose fixing subgroup contains every outside inertia subgroup. -/
theorem originalFullClass_exists_prescribed_norm_inertia_subfield
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (hsys : OriginalFiniteNormalizedClassSystem K L)
    (U : Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K)))
    (hU : (originalIdeleClassNormLinear K L).range ≤ U)
    (hOutside : ∀ z, (originalOutsideIdeleClassRepHom K K S hS).hom z ∈ U) :
    ∃ (H : Subgroup Gal(L/K)) (hH : H.Normal),
      letI : H.Normal := hH
      (originalIdeleClassNormLinear K (IntermediateField.fixedField H)).range = U ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ T → w.asIdeal.inertia Gal(L/K) ≤ H := by
  obtain ⟨ψ, hD, hψ, hl, _⟩ := originalNormalizedClass_completion_norm_system K L p hG hsys
  let r := originalFullClassSpecifiedNormMap K L ψ p hG hD
  obtain ⟨_, hker, himage⟩ := originalFullClassSpecifiedNormMap_properties K L ψ p hG hD
  let V := U.toAddSubgroup.map r
  let H := V.toSubgroup.comap (Abelianization.of : Gal(L/K) →* Abelianization Gal(L/K))
  haveI : H.Normal := inferInstance
  refine ⟨H, inferInstance, ?_, ?_⟩
  · ext c
    change (∃ b, originalIdeleClassNormLinear K (IntermediateField.fixedField H) b = c) ↔ c ∈ U
    rw [originalFullClass_fixedField_norm_preimage K L H r hker (himage H inferInstance),
      originalAbelianization_subgroup_preimage_range V]
    constructor
    · rintro ⟨d, hd, he⟩
      have hz : r (c - d) = 0 :=
        (map_sub r c d).trans ((congrArg (fun z => r c - z) he).trans (sub_self (r c)))
      obtain ⟨b, hb⟩ := (hker _).mp hz
      exact (sub_add_cancel c d) ▸ U.add_mem (hU ⟨b, hb⟩) hd
    · intro hc
      exact ⟨c, hc, rfl⟩
  · intro w hw σ hσ
    have hc := originalCompletion_norm_comparison_with_constructed_closure K L w p hG ψ hD hψ hl
    obtain ⟨c, ⟨z, hz⟩, he⟩ := originalInertia_image_mem_base_outside_norm_image
      K L S T hS hT hST w p hG ψ hD hw hc σ hσ
    change Additive.ofMul (Abelianization.of σ) ∈ U.toAddSubgroup.map r
    refine ⟨c, ?_, he⟩
    exact hz ▸ hOutside z

end
end Dubon2026
