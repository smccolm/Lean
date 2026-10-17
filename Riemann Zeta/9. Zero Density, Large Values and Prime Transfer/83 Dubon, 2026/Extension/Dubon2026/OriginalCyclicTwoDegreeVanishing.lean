import Dubon2026.CyclicPositiveCohomologyVanishing

/-! # The cyclic case of the two-degree vanishing criterion

The finite class/Ext converse reduces cohomological triviality along
cyclic normal subgroups. Pinned cyclic resolutions and the existing odd
degree comparison give the positive-degree conclusion and literal norm
preimages from H1/H2 vanishing. These are the cyclic inputs to that
subgroup induction, not a class-formation duality theorem.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (A : Rep.{0} k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include g hg in
/-- For the actual finite cyclic coefficient, zero H2 gives literal norm preimages of every invariant. -/
theorem originalCyclic_norm_preimages_of_second_zero
    (hsecond : Limits.IsZero (groupCohomology A 2))
    (x : A) (hx : x ∈ A.ρ.invariants) : ∃ y : A, A.norm.hom y = x := by
  have hxg : A.ρ g x = x := hx g
  let v : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := ⟨x, by
    change A.ρ g x - x = 0
    exact sub_eq_zero.mpr hxg⟩
  apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff A g hg 2 (by decide) v).mp
  have hz := hsecond.eq_zero_of_tgt (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide))
  exact congrArg (fun f => f v) hz

include g hg in
/-- Actual H1 and H2 vanishing give every positive cyclic cohomology group zero through the existing periodic resolution. -/
theorem originalCyclic_positive_zero_of_first_second
    (hfirst : Limits.IsZero (groupCohomology A 1))
    (hsecond : Limits.IsZero (groupCohomology A 2)) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  cyclic_positiveCohomology_zero A g hg
    (originalCyclic_norm_preimages_of_second_zero A g hg hsecond) hfirst (n + 1) (Nat.succ_pos n)

end
end Dubon2026
