/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
Adapted from ClassFieldTheory dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/GaloisCohomology/GroupTheory/Finite.lean.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index

/-! # The proper-subgroup obstruction in cyclic prime-power extensions

This finite-group input reduces full decomposition in a cyclic prime-power
extension to full decomposition in its degree-prime subfield. That prime
will supply the local full-order class in DUB-17's class-invariant route.
-/

namespace Dubon2026

/-- A proper subgroup of a cyclic prime-power group lies in its index-prime subgroup. -/
theorem originalCyclicPrimePower_subgroup_le_index_prime
    {G : Type*} [Group G] [IsCyclic G] {p exponent : ℕ}
    (hp : p.Prime) (hcard : Nat.card G = p ^ exponent)
    (P D : Subgroup G) (hPindex : P.index = p) (hD : D ≠ ⊤) : D ≤ P := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgtop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).2 hg
  obtain ⟨n, hn⟩ := (Subgroup.le_zpowers_iff g D).1 (by rw [hgtop]; exact le_top)
  have hgorder : orderOf g = p ^ exponent :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  have hngcd : n.gcd (orderOf g) ≠ 1 := by
    intro h
    apply hD
    rw [hn]
    apply top_unique
    rw [← hgtop, Subgroup.zpowers_le]
    exact mem_zpowers_pow_iff.mpr h
  have hpdiv : p ∣ n := by
    by_contra hpnot
    apply hngcd
    rw [hgorder]
    exact (((hp.coprime_iff_not_dvd).2 hpnot).symm.pow_right exponent).gcd_eq_one
  obtain ⟨k, rfl⟩ := hpdiv
  rw [hn]
  apply Subgroup.zpowers_le.mpr
  have hpow := P.pow_index_mem (g ^ k)
  rw [hPindex] at hpow
  have heq : (g ^ k) ^ p = g ^ (p * k) := by simp only [← pow_mul, Nat.mul_comm]
  rw [← heq]
  exact hpow

end Dubon2026
