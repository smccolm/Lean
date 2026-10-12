import Dubon2026.RationalCyclicInvariant
import Dubon2026.ZModCarryPeriod
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Exact rational character evaluation through the original cyclic carry sum -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

/-- Evaluating an arbitrary finite character on the original cyclic
index is exactly the carry-sum multiplier on its rational invariant.
The identity takes place in the actual rational circle and retains
both original moduli. -/
theorem cyclicCharacter_rationalInvariant_pairing
    {G : Type} [Group G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {N n : ℕ} [NeZero N] [NeZero n] (hN : Nat.card G = N)
    (χ : G →* Multiplicative (ZMod n)) (j : ZMod N) :
    rationalCyclicInvariant n
      (χ (zmodMulEquivOfGenerator hg hN (Multiplicative.ofAdd j))).toAdd =
        (∑ i ∈ Finset.range (orderOf g),
          zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd) •
            rationalCyclicInvariant N j := by
  have he : zmodMulEquivOfGenerator hg hN (Multiplicative.ofAdd j) = g ^ j.val := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, zpow_natCast] using
      zmodMulEquivOfGenerator_apply_ofAdd_intCast hg hN (j.val : ℤ)
  have hz : orderOf g • (χ g).toAdd = 0 := by
    have h := congrArg (fun x => (χ x).toAdd) (pow_orderOf_eq_one g)
    simpa only [map_pow, toAdd_pow, map_one, toAdd_one] using h
  have hsum := zmodAdditionCarry_sum_period (χ g).toAdd (orderOf g) hz
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, hN] at hsum
  have hq : (n : ℚ) * (∑ i ∈ Finset.range (orderOf g),
      zmodAdditionCarry (i • (χ g).toAdd) (χ g).toAdd : ℕ) =
      (N : ℚ) * (χ g).toAdd.val := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hN]
    exact_mod_cast hsum
  rw [he, map_pow, toAdd_pow, map_nsmul, rationalCyclicInvariant_apply,
    rationalCyclicInvariant_apply, ← AddCircle.coe_nsmul, ← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul]
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [nsmul_eq_mul] at hq
  field_simp
  nlinarith [congrArg (fun q : ℚ => (j.val : ℚ) * q) hq]

end
end Dubon2026
