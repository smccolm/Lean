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

import Dubon2026.TameWildOrder
import Dubon2026.TameHigherCongruence
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois

namespace Dubon2026

open IsDedekindDomain
open scoped NumberField

variable {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

theorem heightOne_isWild_of_forall_smul_sub_mem_sq {τ : L ≃ₐ[ℚ] L} (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[ℚ] L))
    (h1 : ∀ x : 𝓞 L, τ • x - x ∈ w.asIdeal ^ 2) :
    Wild.IsWild (w.valuation L) τ := by

  have hint : ∀ x : 𝓞 L, x ≠ 0 →
      w.valuation L ((τ (x : L)) - x)
        < w.valuation L (x : L) := by
    intro x hx0

    have hne : w.intValuation x ≠ 0 := w.intValuation_ne_zero x hx0
    obtain ⟨z, hz⟩ : ∃ z : ℤ, w.intValuation x = WithZero.exp z :=
      ⟨WithZero.log (w.intValuation x), (WithZero.exp_log hne).symm⟩
    have hz0 : z ≤ 0 := by
      have := w.intValuation_le_one x
      rw [hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      exact this
    obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨z.natAbs, by omega⟩
    rw [hk] at hz
    have hxk : x ∈ w.asIdeal ^ k := by
      rw [← w.intValuation_le_pow_iff_mem, hz]
    have h2 : τ • x - x ∈ w.asIdeal ^ (k + 1) := TameKernel.smul_sub_mem_pow_succ_of_forall w.asIdeal hτ h1 k hxk
    rw [← w.intValuation_le_pow_iff_mem] at h2
    have h3 : w.intValuation (τ • x - x) < w.intValuation x := by
      rw [hz]; exact lt_of_le_of_lt h2 (by rw [WithZero.exp_lt_exp]; omega)

    have h4 : HeightOneSpectrum.valuation L w ((τ (x : L)) - x) < HeightOneSpectrum.valuation L w (x : L) := by
      have e1 : τ (x : L) - x = algebraMap (𝓞 L) L (τ • x - x) := by
        rfl
      have e2 : (x : L) = algebraMap (𝓞 L) L x := rfl
      rw [e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      exact h3
    exact h4

  set v := w.valuation L with hv
  intro z hz
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) z
  have hy0 : (y : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : (x : 𝓞 L) ≠ 0 := by
    rintro rfl; simp at hz
  have hx := hint x hx0
  have hy' := hint y hy0

  set x' : L := algebraMap (𝓞 L) L x with hx'
  set y' : L := algebraMap (𝓞 L) L y with hy''
  have hxL : (x : L) = x' := rfl
  have hyL : (y : L) = y' := rfl
  rw [hxL] at hx; rw [hyL] at hy'
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := IsFractionRing.injective (𝓞 L) L
  have hy'0 : y' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hy0
  have hx'0 : x' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
  have hvy : v (τ y') = v y' := by
    have h := Valuation.map_add_eq_of_lt_right v hy'
    rwa [sub_add_cancel] at h
  have hvx' : v x' ≠ 0 := (map_ne_zero v).mpr hx'0
  have hvy' : v y' ≠ 0 := (map_ne_zero v).mpr hy'0

  have hu : v (τ x' / x' - 1) < 1 := by
    rw [div_sub_one hx'0, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvx')]; exact hx
  have hu' : v (τ y' / y' - 1) < 1 := by
    rw [div_sub_one hy'0, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvy')]; exact hy'
  have hτy0 : τ y' ≠ 0 := by simpa using hy'0
  have hvu' : v (τ y' / y') = 1 := by rw [map_div₀, hvy, div_self hvy']

  have e : τ (x' / y') - x' / y' = (x' / y') * ((τ x' / x') / (τ y' / y') - 1) := by
    rw [map_div₀]; field_simp
  have hlast : v ((τ x' / x') / (τ y' / y') - 1) < 1 := by
    have e2 : (τ x' / x') / (τ y' / y') - 1 = ((τ x' / x' - 1) - (τ y' / y' - 1)) / (τ y' / y') := by
      field_simp
      ring
    rw [e2, map_div₀, hvu', div_one]
    exact Valuation.map_sub_lt v hu hu'
  rw [e, map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.mpr ((map_ne_zero v).mpr (div_ne_zero hx'0 hy'0))) hlast

end Dubon2026
