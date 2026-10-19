/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean.
Modified for Dubon: extract the required dependency closure, use the native namespace,
remove external elaboration macros and linter overrides, and retain default proof limits.
This supplies the finite tame local condition for arithmetic patching -> higher symmetric
power continuation -> Dubon Theorem 2.6 (DUB-17) and Corollary 8.2 (DUB-18).
-/

import Mathlib

namespace Dubon2026.TameKernel

universe u v

section Core
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]

theorem smul_mem_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓) : σ • z ∈ 𝔓 := by
  have h : σ • z - z ∈ 𝔓 := hσ z
  have : σ • z = (σ • z - z) + z := by ring
  rw [this]; exact 𝔓.add_mem h hz

theorem smul_mem_sq_of_mem_inertia (𝔓 : Ideal B) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {z : B} (hz : z ∈ 𝔓 ^ 2) :
    σ • z ∈ 𝔓 ^ 2 := by

  let f : B →+* B := MulSemiringAction.toRingHom G B σ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz'
    exact smul_mem_of_mem_inertia 𝔓 hσ hz'
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

theorem pow_sub_pow_mem_sq (𝔓 : Ideal B) {a b : B} (hab : a - b ∈ 𝔓) {N : ℕ} (hN : (N : B) ∈ 𝔓) :
    a ^ N - b ^ N ∈ 𝔓 ^ 2 := by
  set m := a - b with hm
  have ha : a = b + m := by rw [hm]; ring
  rw [ha, add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  refine Ideal.sum_mem _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  rcases Nat.lt_or_ge (N - k) 2 with hlt | hge
  ·
    have hk1 : N - k = 1 := by omega
    have hkN : k = N - 1 := by omega
    have hch : (N.choose k : B) = N := by
      rw [hkN, Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right]
    rw [hk1, pow_one, hch, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hab) hN
  ·
    have : m ^ (N - k) ∈ 𝔓 ^ 2 := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
      rw [hj, pow_add]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hab 2)
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ this)

theorem smul_sub_mem_sq_of_mem_inertia (𝔓 : Ideal B) [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)]
    {ϖ : B} (hϖP : ϖ ∈ 𝔓) (hϖ : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2)
    {σ : G} (hσ : σ ∈ 𝔓.inertia G) (hσϖ : σ • ϖ - ϖ ∈ 𝔓 ^ 2) (x : B) :
    σ • x - x ∈ 𝔓 ^ 2 := by
  classical
  letI : Field (B ⧸ 𝔓) := Ideal.Quotient.field 𝔓
  letI : Fintype (B ⧸ 𝔓) := Fintype.ofFinite _
  set N := Fintype.card (B ⧸ 𝔓) with hNdef

  have hN : (N : B) ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hNdef]
    exact Nat.cast_card_eq_zero (B ⧸ 𝔓)

  have hF : x ^ N - x ∈ 𝔓 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hNdef, FiniteField.pow_card, sub_self]

  obtain ⟨y, hy⟩ := hϖ (x - x ^ N) (by rw [← neg_sub]; exact 𝔓.neg_mem hF)
  set e := x - x ^ N - ϖ * y with he
  have hx : x = x ^ N + ϖ * y + e := by rw [he]; ring

  have h1 : σ • (x ^ N) - x ^ N ∈ 𝔓 ^ 2 := by
    rw [smul_pow']
    exact pow_sub_pow_mem_sq 𝔓 (hσ x) hN
  have h2 : σ • (ϖ * y) - ϖ * y ∈ 𝔓 ^ 2 := by
    have : σ • (ϖ * y) - ϖ * y = (σ • ϖ - ϖ) * (σ • y) + ϖ * (σ • y - y) := by
      rw [smul_mul']; ring
    rw [this]
    refine 𝔓 ^ 2 |>.add_mem (Ideal.mul_mem_right _ _ hσϖ) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hϖP (hσ y)
  have h3 : σ • e - e ∈ 𝔓 ^ 2 := (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) hy
  have : σ • x - x = (σ • (x ^ N) - x ^ N) + (σ • (ϖ * y) - ϖ * y) + (σ • e - e) := by
    conv_lhs => rw [hx]
    rw [smul_add, smul_add]; ring
  rw [this]
  exact (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem h1 h2) h3

end Core


end Dubon2026.TameKernel
