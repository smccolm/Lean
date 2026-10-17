import Dubon2026.OriginalFullClassAbelianNormMap
import Dubon2026.OriginalIdeleNormTower

/-! # Literal fixed-field norms are preimages of subgroup images

The proved norm-map kernel and fixed-field image, together with the
existing actual norm tower, give an elementwise norm criterion. This is
the exact finite correspondence needed to choose the fixed field with a
prescribed norm subgroup on DUB-17's support-removal route.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- The actual fixed-field norm range is exactly the preimage of its
subgroup image under a map with the proved literal full-field norm kernel. -/
theorem originalFullClass_fixedField_norm_preimage
    (r : Additive (OriginalNumberFieldIdeleClassGroup K) →+ Additive (Abelianization Gal(L/K)))
    (hker : ∀ c, r c = 0 ↔ ∃ b, originalIdeleClassNormLinear K L b = c)
    (himage : Set.range (fun c =>
        r (originalIdeleClassNormLinear K (IntermediateField.fixedField S) c)) =
      Set.range (Abelianization.map S.subtype).toAdditive)
    (c : Additive (OriginalNumberFieldIdeleClassGroup K)) :
    (∃ b, originalIdeleClassNormLinear K (IntermediateField.fixedField S) b = c) ↔
      r c ∈ Set.range (Abelianization.map S.subtype).toAdditive := by
  let F := IntermediateField.fixedField S
  haveI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup S
  constructor
  · rintro ⟨b, rfl⟩
    exact himage ▸ ⟨b, rfl⟩
  · intro hc
    obtain ⟨b, hb⟩ := himage.symm ▸ hc
    have hz : r (c - originalIdeleClassNormLinear K F b) = 0 := by
      have hb' : r (originalIdeleClassNormLinear K F b) = r c := hb
      exact (map_sub r c (originalIdeleClassNormLinear K F b)).trans
        ((congrArg (fun z => r c - z) hb').trans (sub_self (r c)))
    obtain ⟨d, hd⟩ := (hker _).mp hz
    refine ⟨originalIdeleClassNormLinear F L d + b, ?_⟩
    rw [map_add]
    have ht : originalIdeleClassNormLinear K F (originalIdeleClassNormLinear F L d) =
        originalIdeleClassNormLinear K L d :=
      congrArg Additive.ofMul (originalIdeleClassNorm_tower K F L d.toMul)
    rw [ht, hd]
    exact sub_add_cancel c (originalIdeleClassNormLinear K F b)

end
end Dubon2026
