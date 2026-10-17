import Dubon2026.OriginalCompletionClassMap
import Dubon2026.OriginalOutsideUnitFixedDescent

/-! # Actual single-place integral units lie in the outside-unit class image

The existing local-coordinate splitting supplies a literal outside-unit
preimage. This is the coefficient input needed to descend local norm-map
traces in DUB-17's inertia and prescribed-support construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- A literal local integral unit outside the support maps to an actual
outside-unit class, with its preimage constructed from local coordinates. -/
theorem originalCompletionClass_integral_mem_outside
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ S)
    (u : (w.adicCompletion L)ˣ) (hu : u ∈ (w.adicCompletionIntegers L).units) :
    (originalCompletionClassRepHom K L w).hom (Additive.ofMul u) ∈
      LinearMap.range (originalOutsideIdeleClassRepHom K L S hS).hom.toLinearMap := by
  have hs : originalIdeleSingleFinite L w u ∈ numberFieldSupportedIdeles L S := by
    simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v _
    by_cases hv : v = w
    · subst v
      rw [originalIdeleSingleFinite_same]
      exact hu
    · rw [originalIdeleSingleFinite_ne L w v hv]
      exact Subgroup.one_mem _
  let y : originalSupportedIdeleRep K L S hS := Additive.ofMul ⟨originalIdeleSingleFinite L w u, hs⟩
  let e := supportedIdeleLocalFactorLinearEquiv L S
  have hz : (e y).1 = 0 := by
    funext p
    cases p with
    | inl v =>
      change Additive.ofMul (numberFieldIdeleInfiniteComponent L v (originalIdeleSingleFinite L w u)) = 0
      rw [originalIdeleSingleFinite_infinite]
      rfl
    | inr v =>
      change Additive.ofMul (numberFieldIdeleFiniteComponent L v.val (originalIdeleSingleFinite L w u)) = 0
      have hv : v.val ≠ w := fun h => hw (h ▸ v.property)
      rw [originalIdeleSingleFinite_ne L w v.val hv]
      rfl
  let x : supportedOutsideUnitRep K L S hS := (e y).2
  have hx : (originalOutsideSupportedInclusion K L S hS).hom x = y := by
    apply e.injective
    change e (e.symm (0, x)) = e y
    rw [e.apply_symm_apply]
    exact Prod.ext hz.symm rfl
  refine ⟨x, ?_⟩
  change (originalSupportedClassRepHom K L S hS).hom
    ((originalOutsideSupportedInclusion K L S hS).hom x) = _
  rw [hx]
  rfl

end
end Dubon2026
