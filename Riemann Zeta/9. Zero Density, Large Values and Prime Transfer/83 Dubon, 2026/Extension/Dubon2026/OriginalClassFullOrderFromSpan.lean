import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # Recover full original class order from the constructed generator

The actual cardinality and singleton span give the full-order input of
the existing normalized subgroup-invariant theorem. This is the precise
bridge used after DUB-17's arithmetic auxiliary-field construction.
-/
namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- An actual original class generator has full extension-degree order when the original H2 cardinality equals that degree. -/
theorem originalIdeleClass_full_order_of_span
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E]
    (y : groupCohomology (originalIdeleClassRep K E) 2)
    (hc : Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E)
    (hs : Submodule.span ℤ {y} = ⊤) : addOrderOf y = Module.finrank K E := by
  have hg : ∀ z : groupCohomology (originalIdeleClassRep K E) 2,
      z ∈ AddSubgroup.zmultiples y := by
    intro z
    obtain ⟨m, hm⟩ := (Submodule.span_singleton_eq_top_iff ℤ y).mp hs z
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    simpa only [Int.cast_id] using (Int.cast_smul_eq_zsmul ℤ m y).symm.trans hm
  exact (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hc

end
end Dubon2026
