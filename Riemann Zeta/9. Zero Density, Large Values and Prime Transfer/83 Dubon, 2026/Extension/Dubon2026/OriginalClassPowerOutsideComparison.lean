import Dubon2026.OriginalSupportedPowerDecomposition
import Dubon2026.OriginalPowerLocalUnitNormQuotient

/-! # The original local-power class subgroup is powers plus outside units

The literal coordinate decomposition gives one containment. The other
uses a supported representative of each actual class, not an assumed
idele decomposition. This identifies the precise subgroup whose index
enters DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)

/-- The literal original local-power class subgroup equals the sum of
the actual power range and outside-unit range at a class-surjective support. -/
theorem originalClassPowerLocalUnitSubmodule_eq_power_sup_outside
    (n : ℕ) (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S)) :
    originalIdeleClassPowerLocalUnitSubmodule K n S ∅ =
      LinearMap.range ((n : ℤ) • (LinearMap.id :
        originalIdeleClassRep K K →ₗ[ℤ] originalIdeleClassRep K K)) ⊔
      LinearMap.range (originalOutsideIdeleClassRepHom K K S hS).hom.toLinearMap := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, hx⟩ := hx
    have hSupport : a ∈ numberFieldSupportedIdeles K S := by
      have h := ((originalIdelePowerLocalUnitSubgroup_mem_iff K n S ∅ a).mp ha).2.2
      simpa only [numberFieldSupportedIdeles, Subgroup.mem_iInf,
        Subgroup.mem_comap, Finset.union_empty] using h
    let A : originalSupportedIdeleRep K K S hS := Additive.ofMul ⟨a, hSupport⟩
    obtain ⟨b, u, hbu⟩ := originalSupportedPowerLocalUnit_decomposition K S hS n A ha
    let q := (originalSupportedClassRepHom K K S hS).hom.toLinearMap
    have hq : q A = x := congrArg Additive.ofMul hx
    have he : q A = n • q b + (originalOutsideIdeleClassRepHom K K S hS).hom u := by
      rw [hbu, q.map_add, map_nsmul q]
      rfl
    apply (Submodule.mem_sup (M := originalIdeleClassRep K K)).mpr
    refine ⟨n • q b, ⟨q b, ?_⟩,
      (originalOutsideIdeleClassRepHom K K S hS).hom u, ⟨u, rfl⟩, he.symm.trans hq⟩
    change (n : ℤ) • q b = n • q b
    exact natCast_zsmul (q b) n
  · apply sup_le
    · rintro x ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hClasses c.toMul
      have hn : a.val ^ n ∈ originalIdelePowerLocalUnitSubgroup K n S ∅ := by
        apply (originalIdelePowerLocalUnitSubgroup_mem_iff K n S ∅ _).mpr
        refine ⟨fun w => ?_, fun v _ => ?_, ?_⟩
        · exact ⟨numberFieldIdeleInfiniteComponent K w a.val,
            (map_pow (numberFieldIdeleInfiniteComponent K w) a.val n).symm⟩
        · exact ⟨numberFieldIdeleFiniteComponent K v a.val,
            (map_pow (numberFieldIdeleFiniteComponent K v) a.val n).symm⟩
        · intro v hv
          have hp := a.property
          simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] at hp
          rw [map_pow]
          exact (v.adicCompletionIntegers K).units.pow_mem
            (hp v (fun h => hv (Finset.mem_union_left ∅ h))) n
      change ((n : ℤ) • c).toMul ∈ originalIdeleClassPowerLocalUnitSubgroup K n S ∅
      refine ⟨a.val ^ n, hn, ?_⟩
      rw [map_pow]
      change (numberFieldSupportedIdeleClassMap K S a) ^ n = _
      rw [ha]
      exact (congrArg Additive.toMul (natCast_zsmul c n)).symm
    · rintro x ⟨u, rfl⟩
      let a := (originalOutsideSupportedInclusion K K S hS).hom u
      have he : supportedIdeleLocalFactorLinearEquiv K S a = (0, u) :=
        (supportedIdeleLocalFactorLinearEquiv K S).apply_symm_apply (0, u)
      refine ⟨a.toMul.val, ?_, rfl⟩
      apply (originalIdelePowerLocalUnitSubgroup_mem_iff K n S ∅ _).mpr
      refine ⟨fun w => ?_, fun v hv => ?_, ?_⟩
      · have h := congrArg (fun z => z.1 (Sum.inl w)) he
        change Additive.ofMul (numberFieldIdeleInfiniteComponent K w a.toMul.val) = 0 at h
        rw [show numberFieldIdeleInfiniteComponent K w a.toMul.val = 1 from
          congrArg Additive.toMul h]
        exact ⟨1, one_pow n⟩
      · have h := congrArg (fun z => z.1 (Sum.inr (⟨v, hv⟩ : S))) he
        change Additive.ofMul (numberFieldIdeleFiniteComponent K v a.toMul.val) = 0 at h
        rw [show numberFieldIdeleFiniteComponent K v a.toMul.val = 1 from
          congrArg Additive.toMul h]
        exact ⟨1, one_pow n⟩
      · intro v hv
        have hp := a.toMul.property
        simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] at hp
        exact hp v (fun h => hv (Finset.mem_union_left ∅ h))

end
end Dubon2026
