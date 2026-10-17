import Dubon2026.OriginalOutsideClassExactSequence

/-! # Enlarging support shrinks the actual outside-unit class image

The literal supported-idele coordinates give this containment without
an assumed map of quotients. It is the input needed to reduce the large
Kummer norm field to the prescribed smaller support on DUB-17's chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K : Type) [Field K] [NumberField K]
  (S T : Finset (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)
  (hT : ∀ (σ : Gal(K/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ T)

/-- The outside-unit class range is antitone in the actual finite support. -/
theorem originalOutsideIdeleClass_range_antitone (hST : S ⊆ T) :
    LinearMap.range (originalOutsideIdeleClassRepHom K K T hT).hom.toLinearMap ≤
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  rintro c ⟨u, rfl⟩
  let a := (originalOutsideSupportedInclusion K K T hT).hom u
  have ha : supportedIdeleLocalFactorLinearEquiv K T a = (0, u) :=
    (supportedIdeleLocalFactorLinearEquiv K T).apply_symm_apply (0, u)
  have hzero (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) :
      numberFieldIdeleFiniteComponent K v a.toMul.val = 1 := by
    have he := congrArg (fun z => z.1 (Sum.inr (⟨v, hv⟩ : T))) ha
    exact congrArg Additive.toMul he
  have hSupported : a.toMul.val ∈ numberFieldSupportedIdeles K S := by
    simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v _
    by_cases hv : v ∈ T
    · rw [hzero v hv]
      exact Subgroup.one_mem _
    · have h := a.toMul.property
      simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] at h
      exact h v hv
  let b : originalSupportedIdeleRep K K S hS := Additive.ofMul ⟨a.toMul.val, hSupported⟩
  let e := supportedIdeleLocalFactorLinearEquiv K S
  have hb : (e b).1 = 0 := by
    funext z
    cases z with
    | inl v =>
      have he := congrArg (fun z => z.1 (Sum.inl v)) ha
      exact he
    | inr v =>
      change Additive.ofMul (numberFieldIdeleFiniteComponent K v.val a.toMul.val) = 0
      rw [hzero v.val (hST v.property)]
      rfl
  let x : supportedOutsideUnitRep K K S hS := (e b).2
  have hx : (originalOutsideSupportedInclusion K K S hS).hom x = b := by
    apply e.injective
    change e (e.symm (0, x)) = e b
    rw [e.apply_symm_apply]
    exact Prod.ext hb.symm rfl
  refine ⟨x, ?_⟩
  change (originalSupportedClassRepHom K K S hS).hom
    ((originalOutsideSupportedInclusion K K S hS).hom x) = _
  rw [hx]
  rfl

end
end Dubon2026
