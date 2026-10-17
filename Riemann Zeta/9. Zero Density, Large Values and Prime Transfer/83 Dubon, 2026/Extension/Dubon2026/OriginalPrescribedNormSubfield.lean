import Dubon2026.OriginalFixedFieldNormPreimage

/-! # An actual intermediate field with a prescribed class-norm subgroup

Any subgroup containing the original full norm range determines a normal
fixed field with precisely that norm range. This uses the proved finite
norm map and its subgroup images. DUB-17 still needs inertia control to
give the field the prescribed ramification support.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module

/-- The preimage of a subgroup of the actual abelianization has exactly
that subgroup as its induced abelianization image. -/
theorem originalAbelianization_subgroup_preimage_range
    {G : Type} [Group G] (T : AddSubgroup (Additive (Abelianization G))) :
    Set.range (Abelianization.map
      ((T.toSubgroup.comap (Abelianization.of : G →* Abelianization G)).subtype)).toAdditive =
      (T : Set (Additive (Abelianization G))) := by
  let S := T.toSubgroup.comap (Abelianization.of : G →* Abelianization G)
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective t.toMul
    change Abelianization.of s = t.toMul at hs
    have ht : t = Additive.ofMul (Abelianization.of s) := (congrArg Additive.ofMul hs).symm
    rw [ht]
    exact s.property
  · intro hz
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective z.toMul
    change Abelianization.of g = z.toMul at hg
    have hm : g ∈ S := by
      change Additive.ofMul (Abelianization.of g) ∈ T
      rw [hg]
      exact hz
    exact ⟨Additive.ofMul (Abelianization.of (⟨g, hm⟩ : S)), congrArg Additive.ofMul hg⟩

/-- The normalized actual class system constructs a normal fixed field
whose literal norm range is any given submodule containing the full norm
range. No ramification or arithmetic-stage placement claim is included. -/
theorem originalFullClass_exists_prescribed_norm_subfield
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (hsys : OriginalFiniteNormalizedClassSystem K L)
    (U : Submodule ℤ (Additive (OriginalNumberFieldIdeleClassGroup K)))
    (hU : (originalIdeleClassNormLinear K L).range ≤ U) :
    ∃ (S : Subgroup Gal(L/K)) (hS : S.Normal),
      letI : S.Normal := hS
      (originalIdeleClassNormLinear K (IntermediateField.fixedField S)).range = U := by
  obtain ⟨r, _, hker, himage⟩ := originalFullClass_abelian_norm_map K L p hG hsys
  let T := U.toAddSubgroup.map r
  let S := T.toSubgroup.comap (Abelianization.of : Gal(L/K) →* Abelianization Gal(L/K))
  haveI : S.Normal := inferInstance
  refine ⟨S, inferInstance, ?_⟩
  ext c
  change (∃ b, originalIdeleClassNormLinear K (IntermediateField.fixedField S) b = c) ↔ c ∈ U
  rw [originalFullClass_fixedField_norm_preimage K L S r hker (himage S inferInstance),
    originalAbelianization_subgroup_preimage_range T]
  constructor
  · rintro ⟨d, hd, he⟩
    have hz : r (c - d) = 0 :=
      (map_sub r c d).trans ((congrArg (fun z => r c - z) he).trans (sub_self (r c)))
    obtain ⟨b, hb⟩ := (hker _).mp hz
    have hm : c - d ∈ U := hU ⟨b, hb⟩
    exact (sub_add_cancel c d) ▸ U.add_mem hm hd
  · intro hc
    exact ⟨c, hc, rfl⟩

end
end Dubon2026
