/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

The quotient map and injectivity proof below adapt the pinned Mathlib
`ZMod.toAddCircle` construction from real to rational coefficients.
-/
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Data.ZMod.Basic

/-! # The actual finite cyclic subgroup of the rational circle -/

namespace Dubon2026
noncomputable section

variable (n : ℕ) [NeZero n]

/-- The literal rational map `j mod n ↦ j/n mod ℤ`. -/
def rationalCyclicInvariant : ZMod n →+ AddCircle (1 : ℚ) :=
  ZMod.lift n ⟨AddMonoidHom.mk' (fun j => ↑(j / n : ℚ)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

/-- The rational invariant retains the original integer representative. -/
theorem rationalCyclicInvariant_intCast (j : ℤ) :
    rationalCyclicInvariant n (j : ZMod n) = ↑(j / n : ℚ) := by
  simp [rationalCyclicInvariant]

/-- Formula for the actual finite representative. -/
theorem rationalCyclicInvariant_apply (j : ZMod n) :
    rationalCyclicInvariant n j = ↑(j.val / n : ℚ) := by
  rw [← ZMod.natCast_zmod_val j]
  simpa using rationalCyclicInvariant_intCast n j.val

/-- The original cyclic invariant is injective in the actual rational circle. -/
theorem rationalCyclicInvariant_injective : Function.Injective (rationalCyclicInvariant n) := by
  intro x y hxy
  have hn : (0 : ℚ) < n := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [rationalCyclicInvariant_apply, rationalCyclicInvariant_apply,
    AddCircle.coe_eq_coe_iff_of_mem_Ico, div_left_inj' hn.ne', Nat.cast_inj,
    (ZMod.val_injective n).eq_iff] at hxy <;>
    exact ⟨by positivity,
      by simpa only [zero_add, div_lt_one hn, Nat.cast_lt] using (ZMod.val_lt _)⟩

/-- The actual image is exactly the subgroup killed by the original positive degree. -/
theorem rationalCyclicInvariant_mem_range_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (rationalCyclicInvariant n).range ↔ n • x = 0 := by
  constructor
  · rintro ⟨j, rfl⟩
    rw [← map_nsmul]
    simp [nsmul_eq_mul]
  · intro hx
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨j, hj⟩ := hx
    have hq : (j : ℚ) / n = q := by
      apply (div_eq_iff (Nat.cast_ne_zero.mpr (NeZero.ne n))).mpr
      simpa only [zsmul_eq_mul, mul_one, nsmul_eq_mul, mul_comm] using hj
    exact ⟨(j : ZMod n), by rw [rationalCyclicInvariant_intCast, hq]⟩

end
end Dubon2026
