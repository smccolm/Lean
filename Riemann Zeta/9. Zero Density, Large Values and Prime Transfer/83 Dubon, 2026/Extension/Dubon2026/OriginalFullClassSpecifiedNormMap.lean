import Dubon2026.OriginalFullClassAbelianNormMap

/-! # Norm-map properties for a specified original fundamental cocycle

The existing norm quotient and subgroup trace proofs apply to any
specified acyclic fundamental cocycle. Keeping that cocycle explicit
allows the normalized completion comparison to control inertia for
the very same map in DUB-17's prescribed-support construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (φ : groupCohomology.cocycles₂ (originalIdeleClassRep K L))
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
  (hv : ∀ H : Subgroup Gal(L/K),
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) φ)) 2))

/-- The actual base-class map for the specified original cocycle. -/
def originalFullClassSpecifiedNormMap :
    Additive (OriginalNumberFieldIdeleClassGroup K) →+ Additive (Abelianization Gal(L/K)) :=
  (originalInvariantAbelianMap (originalIdeleClassRep K L) φ p hG hv).comp
    (originalFullClassBaseInvariantEquiv K L).toAddMonoidHom

/-- The specified map is surjective, has the literal norm kernel and
carries every normal fixed-field norm onto its subgroup image. -/
theorem originalFullClassSpecifiedNormMap_properties :
    let r := originalFullClassSpecifiedNormMap K L φ p hG hv
    Function.Surjective r ∧
      (∀ c, r c = 0 ↔ ∃ b, originalIdeleClassNormLinear K L b = c) ∧
      ∀ (S : Subgroup Gal(L/K)) (hS : S.Normal),
        letI : S.Normal := hS
        Set.range (fun c => r (originalIdeleClassNormLinear K (IntermediateField.fixedField S) c)) =
          Set.range (Abelianization.map S.subtype).toAdditive := by
  classical
  let C := originalIdeleClassRep K L
  let β := originalFullClassBaseInvariantEquiv K L
  let α := originalInvariantAbelianMap C φ p hG hv
  let r := originalFullClassSpecifiedNormMap K L φ p hG hv
  refine ⟨?_, ?_, ?_⟩
  · intro z
    let e := originalInvariantNormAbelianEquiv C φ p hG hv
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (e.symm z)
    refine ⟨β.symm c, ?_⟩
    change originalInvariantAbelianMap C φ p hG hv (β (β.symm c)) = z
    rw [β.apply_symm_apply, originalInvariantAbelianMap_eq_quotient, hc]
    exact e.apply_symm_apply z
  · intro c
    change originalInvariantAbelianMap C φ p hG hv (β c) = 0 ↔ _
    rw [originalInvariantAbelianMap_eq_zero_iff]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, β.injective ((originalFullClassBaseInvariant_norm K L b).trans hb)⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, (originalFullClassBaseInvariant_norm K L b).symm⟩
  · intro S hS
    letI : S.Normal := hS
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype (Gal(L/K) ⧸ S) := Fintype.ofFinite _
    let F := IntermediateField.fixedField S
    have htrace (c : Additive (OriginalNumberFieldIdeleClassGroup F)) :
        β (originalIdeleClassNormLinear K F c) =
          originalInvariantRelativeTrace C S ((originalIdeleClassNormalInvariantInclusion S).hom c) :=
      Subtype.ext (originalFullClass_fixedField_norm_trace S c)
    calc
      Set.range (fun c => r (originalIdeleClassNormLinear K F c)) =
          Set.range (fun x : C.quotientToInvariants S => α (originalInvariantRelativeTrace C S x)) := by
        ext z
        constructor
        · rintro ⟨c, rfl⟩
          exact ⟨(originalIdeleClassNormalInvariantInclusion S).hom c,
            (congrArg α (htrace c)).symm⟩
        · rintro ⟨x, rfl⟩
          obtain ⟨c, rfl⟩ := (originalIdeleClassNormalInvariantInclusion_bijective S).2 x
          exact ⟨c, congrArg α (htrace c)⟩
      _ = _ := originalInvariantAbelianMap_trace_range C φ p hG hv S

end
end Dubon2026
