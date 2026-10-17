import Dubon2026.OriginalInvariantAbelianTrace
import Dubon2026.OriginalFixedFieldNormTrace
import Dubon2026.OriginalFullClassAbelianNormIndex

/-! # An actual full-class norm map with fixed-field subgroup images

The constructed normalized class system supplies one surjective map from
actual base classes to the abelianized Galois group. Its kernel is the
literal full-field norm range, and every normal fixed-field norm has the
corresponding subgroup image. This is the finite ground-norm comparison
needed by DUB-17's prescribed-support norm-field construction; local
inertia control remains separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
  Submodule.Quotient.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A normalized actual class system constructs a surjective abelianized
norm map, with the literal kernel and every normal fixed-field norm image. -/
theorem originalFullClass_abelian_norm_map (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p Gal(L/K)) (hsys : OriginalFiniteNormalizedClassSystem K L) :
    ∃ r : Additive (OriginalNumberFieldIdeleClassGroup K) →+ Additive (Abelianization Gal(L/K)),
      Function.Surjective r ∧
      (∀ c, r c = 0 ↔ ∃ b, originalIdeleClassNormLinear K L b = c) ∧
      ∀ (S : Subgroup Gal(L/K)) (hS : S.Normal),
        letI : S.Normal := hS
        Set.range (fun c => r (originalIdeleClassNormLinear K (IntermediateField.fixedField S) c)) =
          Set.range (Abelianization.map S.subtype).toAdditive := by
  classical
  obtain ⟨u, _, h1, hc, hg, _⟩ := hsys
  let C := originalIdeleClassRep K L
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  obtain ⟨hv, _, _⟩ := originalFundamentalPGroup_positive_and_norm p hG C φ h1 hc hg
  let β := originalFullClassBaseInvariantEquiv K L
  let α := originalInvariantAbelianMap C φ p hG hv
  let r := α.comp β.toAddMonoidHom
  refine ⟨r, ?_, ?_, ?_⟩
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
