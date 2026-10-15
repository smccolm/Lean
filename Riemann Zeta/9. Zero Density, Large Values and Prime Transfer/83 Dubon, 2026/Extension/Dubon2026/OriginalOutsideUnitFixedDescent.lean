import Dubon2026.OriginalSupportedBaseChangeReflection
import Dubon2026.OriginalOutsideClassExactSequence
import Dubon2026.OriginalIdeleClassBaseChange

/-! # Original outside units descend to the actual base field

Fixed original ideles already descend. Reflection of support and the
injective original S-place transition show that the descended idele is
itself an outside unit. This proves the remaining coefficient descent
needed for the class-quotient invariant comparison serving DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)

include hST

/-- A fixed original outside-unit idele is the actual base change of an original base outside-unit idele. -/
theorem originalOutsideUnit_fixed_descends
    (u : supportedOutsideUnitRep K L T hT)
    (hu : ∀ g, (supportedOutsideUnitRep K L T hT).ρ g u = u) :
    ∃ v : supportedOutsideUnitRep K K S hS,
      originalIdeleBaseChangeMap K L
        ((originalOutsideSupportedInclusion K K S hS).hom v).toMul.val =
          ((originalOutsideSupportedInclusion K L T hT).hom u).toMul.val := by
  let y := (originalOutsideSupportedInclusion K L T hT).hom u
  have hfixed (g : Gal(L/K)) :
      numberFieldIdeleGaloisMap K L g y.toMul.val = y.toMul.val := by
    have he := Rep.hom_comm_apply (originalOutsideSupportedInclusion K L T hT) g u
    rw [hu] at he
    exact congrArg (fun z : originalSupportedIdeleRep K L T hT => z.toMul.val) he.symm
  obtain ⟨b, hb⟩ := originalIdeleBaseChangeMap_surjective_fixed K L y.toMul.val hfixed
  have hbs : b ∈ numberFieldSupportedIdeles K S :=
    originalIdeleBaseChangeMap_reflects_supported K L S T hST b
      (hb ▸ y.toMul.property)
  let bs : Additive (numberFieldSupportedIdeles K S) := Additive.ofMul ⟨b, hbs⟩
  have hmap : Additive.ofMul (originalSupportedIdeleBaseChangeMap K L S T
      (fun w hw hv => hw ((hST w).mpr hv)) bs.toMul) = y := by
    apply Additive.toMul.injective
    exact Subtype.ext hb
  let eK := supportedIdeleLocalFactorLinearEquiv K S
  let eL := supportedIdeleLocalFactorLinearEquiv L T
  have hy : (eL y).1 = 0 := congrArg Prod.fst (eL.apply_symm_apply (0, u))
  have hzero : (eK bs).1 = 0 := by
    apply originalSPlaceBaseChange_injective K L S T hST
    rw [map_zero]
    have he := originalSPlaceBaseChange_projection K L S T hST bs
    rw [hmap] at he
    exact he.trans hy
  let v : supportedOutsideUnitRep K K S hS := (eK bs).2
  have hv : (originalOutsideSupportedInclusion K K S hS).hom v = bs := by
    apply eK.injective
    change eK (eK.symm (0, v)) = eK bs
    rw [eK.apply_symm_apply]
    exact Prod.ext hzero.symm rfl
  refine ⟨v, ?_⟩
  rw [hv]
  exact hb

/-- Actual full-class base change reflects the original outside-unit class image. -/
theorem originalFullClassBaseChange_reflects_outside
    (c : OriginalNumberFieldIdeleClassGroup K)
    (hc : Additive.ofMul (originalIdeleClassBaseChangeMap K L c) ∈
      LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap) :
    Additive.ofMul c ∈ LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  obtain ⟨u, hu⟩ := hc
  change (originalOutsideIdeleClassRepHom K L T hT).hom u =
    Additive.ofMul (originalIdeleClassBaseChangeMap K L c) at hu
  have hfixed (g : Gal(L/K)) : (supportedOutsideUnitRep K L T hT).ρ g u = u := by
    apply originalOutsideIdeleClassRepHom_injective K L T hT
    rw [Rep.hom_comm_apply, hu]
    exact congrArg Additive.ofMul (originalIdeleClassBaseChangeMap_fixed K L g c)
  obtain ⟨v, hv⟩ := originalOutsideUnit_fixed_descends K L S T hS hT hST u hfixed
  refine ⟨v, ?_⟩
  apply Additive.toMul.injective
  apply originalIdeleClassBaseChangeMap_injective K L
  change originalIdeleClassBaseChangeMap K L
    (QuotientGroup.mk' (numberFieldPrincipalIdele K).range
      ((originalOutsideSupportedInclusion K K S hS).hom v).toMul.val) = _
  rw [originalIdeleClassBaseChangeMap_mk, hv]
  exact congrArg Additive.toMul hu

end
end Dubon2026
