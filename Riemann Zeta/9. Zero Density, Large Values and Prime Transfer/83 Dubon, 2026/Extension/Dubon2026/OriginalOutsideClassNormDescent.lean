import Dubon2026.OriginalOutsideUnitFixedDescent
import Dubon2026.OriginalFullClassNormQuotientComparison

/-! # Actual outside-unit classes descend under the field norm

The literal norm is a sum of Galois translates after base change.
The existing reflection of the outside-unit image therefore descends
that norm to the prescribed base support. This is the coefficient
comparison needed to transport DUB-17's norm field through an actual
field tower, without transporting its entire normalized class system.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 E)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(E/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow K E w ∈ S)

include hST in
/-- An actual outside-unit class has actual field norm in the base
outside-unit image, for the literal inverse-image support. -/
theorem originalOutsideClass_norm_mem
    (x : originalIdeleClassRep K E)
    (hx : x ∈ LinearMap.range (originalOutsideIdeleClassRepHom K E T hT).hom.toLinearMap) :
    originalIdeleClassNormLinear K E x ∈
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  apply originalFullClassBaseChange_reflects_outside K E S T hS hT hST
    (originalIdeleClassNormLinear K E x).toMul
  have he := congrArg Subtype.val (originalFullClassBaseInvariant_norm K E x)
  change Additive.ofMul (originalIdeleClassBaseChangeMap K E
    (originalIdeleClassNormLinear K E x).toMul) = (originalIdeleClassRep K E).ρ.norm x at he
  rw [he]
  simp only [Representation.norm, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro g _
  exact (originalOutsideIdeleClassRepHom K E T hT).hom.range.apply_mem_toSubmodule g hx

end
end Dubon2026
