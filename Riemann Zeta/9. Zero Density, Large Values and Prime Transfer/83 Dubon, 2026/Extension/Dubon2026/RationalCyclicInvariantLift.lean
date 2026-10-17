import Dubon2026.RationalCyclicInvariant

/-! # Read a finite-order rational-circle invariant in its residue ring

Use the existing exact image of the literal map j to j/n. This supplies
the scalar readout of the actual relation obstruction on DUB-17's duality
route, retaining the source normalization rather than selecting characters.
-/
namespace Dubon2026
noncomputable section
variable (n : ℕ) [NeZero n] {A : Type} [AddCommGroup A]

/-- Every additive invariant killed by n has an additive readout
through the literal rational cyclic invariant. -/
theorem rationalCyclicInvariant_exists_lift (f : A →+ AddCircle (1 : ℚ))
    (hf : ∀ x, n • f x = 0) :
    ∃ g : A →+ ZMod n, ∀ x, rationalCyclicInvariant n (g x) = f x := by
  have he (x : A) : ∃ j, rationalCyclicInvariant n j = f x :=
    (rationalCyclicInvariant_mem_range_iff n (f x)).mpr (hf x)
  let g : A →+ ZMod n := {
    toFun := fun x => (he x).choose
    map_zero' := by
      apply rationalCyclicInvariant_injective n
      rw [(he 0).choose_spec, map_zero, map_zero]
    map_add' := fun x y => by
      apply rationalCyclicInvariant_injective n
      rw [(he (x + y)).choose_spec, map_add, map_add,
        (he x).choose_spec, (he y).choose_spec] }
  exact ⟨g, fun x => (he x).choose_spec⟩

end
end Dubon2026
