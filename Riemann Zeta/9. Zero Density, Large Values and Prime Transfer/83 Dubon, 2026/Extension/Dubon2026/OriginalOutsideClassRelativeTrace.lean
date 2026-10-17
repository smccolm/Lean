import Dubon2026.OriginalInvariantAbelianTrace
import Dubon2026.OriginalOutsideUnitFixedDescent
import Dubon2026.OriginalFullClassNormQuotientComparison

/-! # Relative traces of actual outside-unit classes descend

The actual outside-unit image is stable under the Galois action, so its
relative traces stay in that image. The existing fixed-class reflection
then descends the trace to an actual base outside-unit class. This avoids
a separate coordinate formula for DUB-17's local-unit norm-map image.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField BigOperators
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (H : Subgroup Gal(L/K)) [H.Normal] [Fintype (Gal(L/K) ⧸ H)]

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- Relative trace preserves the literal outside-unit class image. -/
theorem originalOutsideClass_relativeTrace_mem
    (x : (originalIdeleClassRep K L).quotientToInvariants H)
    (hx : x.val ∈ LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap) :
    (originalInvariantRelativeTrace (originalIdeleClassRep K L) H x).val ∈
      LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap := by
  let C := originalIdeleClassRep K L
  change (((C.quotientToInvariants H).ρ.norm x).val) ∈ _
  simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
  apply Submodule.sum_mem
  intro q _
  rw [originalQuotientInvariant_action_out C H q x]
  exact (originalOutsideIdeleClassRepHom K L T hT).hom.range.apply_mem_toSubmodule q.out hx

/-- The actual base class descending an outside-unit relative trace
itself has an actual outside-unit representative. -/
theorem originalOutsideClass_relativeTrace_base_mem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
    (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K L w ∈ S)
    (x : (originalIdeleClassRep K L).quotientToInvariants H)
    (hx : x.val ∈ LinearMap.range (originalOutsideIdeleClassRepHom K L T hT).hom.toLinearMap) :
    (originalFullClassBaseInvariantEquiv K L).symm
      (originalInvariantRelativeTrace (originalIdeleClassRep K L) H x) ∈
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  let β := originalFullClassBaseInvariantEquiv K L
  let y := originalInvariantRelativeTrace (originalIdeleClassRep K L) H x
  apply originalFullClassBaseChange_reflects_outside K L S T hS hT hST (β.symm y).toMul
  have he := congrArg Subtype.val (β.apply_symm_apply y)
  change Additive.ofMul (originalIdeleClassBaseChangeMap K L (β.symm y).toMul) = y.val at he
  rw [he]
  exact originalOutsideClass_relativeTrace_mem K L T hT H x hx

end
end Dubon2026
