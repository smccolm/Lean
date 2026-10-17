import Dubon2026.RationalCyclicInvariant
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Cyclicity of the finite rational-circle character image

The character cutting out the two-primary cyclotomic splitting field has
finite image in the actual rational circle. The existing rational cyclic
invariant identifies that image with a subgroup of a finite cyclic group.
This discharges the cyclic-image input to DUB-17's arithmetic class route.
-/
namespace Dubon2026
noncomputable section

/-- A finite subgroup of the literal rational circle is cyclic, by the
already proved rational invariant with denominator its cardinality. -/
theorem originalRationalCircle_finite_subgroup_cyclic
    (H : AddSubgroup (AddCircle (1 : ℚ))) [Finite H] : IsAddCyclic H := by
  let n := Nat.card H
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  let f := rationalCyclicInvariant n
  haveI : IsAddCyclic f.range :=
    isAddCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hle : H ≤ f.range := by
    intro x hx
    apply (rationalCyclicInvariant_mem_range_iff n x).mpr
    exact congrArg Subtype.val (show Nat.card H • (⟨x, hx⟩ : H) = 0 from card_nsmul_eq_zero')
  exact isAddCyclic_of_injective (AddSubgroup.inclusion hle)
    (AddSubgroup.inclusion_injective hle)

end
end Dubon2026
