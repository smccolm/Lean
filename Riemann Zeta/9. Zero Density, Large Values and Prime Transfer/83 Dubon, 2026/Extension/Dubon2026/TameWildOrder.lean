/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom.lean.
Modified for Dubon: extract the required dependency closure, use the native namespace,
remove external elaboration macros and linter overrides, and retain default proof limits.
This supplies the finite tame local condition for arithmetic patching -> higher symmetric
power continuation -> Dubon Theorem 2.6 (DUB-17) and Corollary 8.2 (DUB-18).
-/

import Mathlib

namespace Dubon2026.Wild

variable {K L : Type} [Field K] [Field L] [Algebra K L] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)

/-- An automorphism is wild when its displacement of each nonzero field element has strictly smaller valuation. -/
def IsWild (σ : L ≃ₐ[K] L) : Prop := ∀ z : L, z ≠ 0 → v (σ z - z) < v z

theorem IsWild.valuation_apply {σ : L ≃ₐ[K] L} (hw : IsWild v σ) (w : L) : v (σ w) = v w := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  have h := Valuation.map_add_eq_of_lt_right v (hw w hw0)
  rwa [sub_add_cancel] at h

theorem IsWild.pow {σ : L ≃ₐ[K] L} (hw : IsWild v σ) (n : ℕ) : IsWild v (σ ^ n) := by
  induction n with
  | zero => intro z hz; simp [(map_ne_zero v).mpr hz, zero_lt_iff]
  | succ n ih =>
    intro z hz
    have hsplit : (σ ^ (n + 1)) z - z = σ ((σ ^ n) z - z) + (σ z - z) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ (hw z hz)
    rw [IsWild.valuation_apply v hw]
    exact ih z hz

theorem valuation_natCast_le_one (m : ℕ) : v (m : L) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih (by rw [v.map_one]))

theorem valuation_intCast_le_one (m : ℤ) : v (m : L) ≤ 1 := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [Int.cast_natCast]; exact valuation_natCast_le_one v k
  · rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact valuation_natCast_le_one v k

theorem valuation_natCast_eq_one_of_coprime {q m : ℕ} (hq : v (q : L) < 1) (hm : Nat.Coprime m q) :
    v (m : L) = 1 := by
  have hle : v (m : L) ≤ 1 := valuation_natCast_le_one v m
  by_contra hne
  have hlt : v (m : L) < 1 := lt_of_le_of_ne hle hne
  have hg : (Int.gcd m q : ℤ) = 1 := by exact_mod_cast hm
  have hb := Int.gcd_eq_gcd_ab m q
  rw [hg] at hb
  have h1 : (1 : L) = (m : L) * (Int.gcdA m q : L) + (q : L) * (Int.gcdB m q : L) := by
    exact_mod_cast congrArg (Int.cast : ℤ → L) hb
  have : v (1 : L) < 1 := by
    rw [h1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hlt (valuation_intCast_le_one v _)
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hq (valuation_intCast_le_one v _)
  rw [map_one] at this
  exact lt_irrefl _ this

theorem IsWild.apply_eq_of_pow_apply_eq {σ : L ≃ₐ[K] L} (hw : IsWild v σ) {q m : ℕ} (hq : v (q : L) < 1)
    (hm : Nat.Coprime m q) (y : L) (hy : (σ ^ m) y = y) : σ y = y := by
  by_contra hne
  set w := σ y - y with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have htel : (Finset.range m).sum (fun i => (σ ^ i) w) = 0 := by
    have h := Finset.sum_range_sub (fun i => (σ ^ i) y) m
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [hy, sub_self] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
  have hdec : (Finset.range m).sum (fun i => (σ ^ i) w)
      = (m : L) * w + (Finset.range m).sum (fun i => (σ ^ i) w - w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hS : v ((Finset.range m).sum (fun i => (σ ^ i) w - w)) < v ((m : L) * w) := by
    rw [map_mul, valuation_natCast_eq_one_of_coprime v hq hm, one_mul]
    exact Valuation.map_sum_lt _ ((map_ne_zero _).mpr hw0) (fun i _ => (IsWild.pow v hw i) w hw0)
  have hval : v ((Finset.range m).sum (fun i => (σ ^ i) w)) = v ((m : L) * w) := by
    rw [hdec, add_comm]
    exact Valuation.map_add_eq_of_lt_right _ hS
  rw [htel, map_zero, map_mul, valuation_natCast_eq_one_of_coprime v hq hm, one_mul, eq_comm, map_eq_zero] at hval
  exact hw0 hval

theorem IsWild.orderOf_eq_pow {σ : L ≃ₐ[K] L} (hw : IsWild v σ) {q : ℕ} (hqp : q.Prime) (hq : v (q : L) < 1)
    (hfin : 0 < orderOf σ) : ∃ a : ℕ, orderOf σ = q ^ a := by
  obtain ⟨a, m, hqm, ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd hfin.ne' q hqp.one_lt.ne'
  have hcop : Nat.Coprime m q := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqm)
  have hw' : IsWild v (σ ^ (q ^ a)) := IsWild.pow v hw (q ^ a)
  have h1 : σ ^ (q ^ a) = 1 := by
    refine AlgEquiv.ext fun y => ?_
    refine IsWild.apply_eq_of_pow_apply_eq v hw' hq hcop y ?_
    rw [← pow_mul, ← ho, pow_orderOf_eq_one]
    rfl
  have h2 : orderOf σ ∣ q ^ a := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hqp).mp h2
  exact ⟨b, hb⟩

end Dubon2026.Wild
