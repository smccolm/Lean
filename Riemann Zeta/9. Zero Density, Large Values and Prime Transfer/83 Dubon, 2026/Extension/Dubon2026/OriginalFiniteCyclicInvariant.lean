import Dubon2026.RationalCyclicInvariant
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Normalized invariants of actual finite cyclic additive groups

Reuse the pinned cyclic quotient lift and the already proved rational-circle
invariant. This is the normalization step after the full-order arithmetic H2
class required for DUB-17's finite class invariants has been constructed.
-/

namespace Dubon2026
noncomputable section

/-- A specified generator gives an injective rational invariant with exact torsion image and normalization. -/
theorem originalFiniteCyclic_exists_invariant
    {A : Type*} [AddCommGroup A] (u : A) (n : ℕ) (hn : 0 < n)
    (hu : addOrderOf u = n) (hgen : ∀ x : A, x ∈ AddSubgroup.zmultiples u) :
    ∃ f : A →+ AddCircle (1 : ℚ), Function.Injective f ∧
      (∀ x : AddCircle (1 : ℚ), x ∈ f.range ↔ n • x = 0) ∧
      (∀ j : ℤ, f (j • u) = ↑(j / n : ℚ)) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let h : ℤ →+ A := zmultiplesHom A u
  have hk : h (n : ℤ) = 0 := by
    change (n : ℤ) • u = 0
    rw [← hu]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mp dvd_rfl
  let φ : ZMod n →+ A := ZMod.lift n ⟨h, hk⟩
  have hφ : ∀ j : ℤ, φ (j : ZMod n) = j • u := fun j => ZMod.lift_coe n ⟨h, hk⟩ j
  have hi : Function.Injective φ := by
    apply (ZMod.lift_injective n).mpr
    intro j hj
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [← hu]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hj
  have hs : Function.Surjective φ := by
    intro x
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen x)
    exact ⟨j, (hφ j).trans hj⟩
  let e := AddEquiv.ofBijective φ ⟨hi, hs⟩
  let f := (rationalCyclicInvariant n).comp e.symm.toAddMonoidHom
  refine ⟨f, (rationalCyclicInvariant_injective n).comp e.symm.injective, ?_, ?_⟩
  · intro x
    rw [← rationalCyclicInvariant_mem_range_iff n]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨e.symm a, ha⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, by simpa only [f, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddEquiv.symm_apply_apply] using hj⟩
  · intro j
    change rationalCyclicInvariant n (e.symm (j • u)) = _
    rw [← hφ j]
    exact (congrArg (rationalCyclicInvariant n) (e.symm_apply_apply (j : ZMod n))).trans
      (rationalCyclicInvariant_intCast n j)

end
end Dubon2026
