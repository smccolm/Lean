/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.RationalCircleElementCharacter
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # A two-power cyclotomic character detecting conjugation

Adapted from Tau Ceti revision 5f93ad556efb2f77494162e13d1e0c7ac37d5ff2,
`TauCeti/Data/ZMod/TwoPowerCharacter.lean`, to the unchanged pinned Mathlib.
The character's kernel has order at most two and excludes minus one.
Its fixed field will provide the totally complex cyclic splitting stage
needed for the two-primary part of the full-order arithmetic class in
DUB-17's finite class/Ext duality chain. No splitting field or full-order
cohomology class is asserted by this character construction alone.
-/
namespace Dubon2026
noncomputable section

/-- A character of the units modulo `2^(n+3)` detects complex conjugation and has kernel of
order at most two. Its value on `5` has order `2^(n+1)`. -/
theorem originalTwoPowerUnits_exists_character (n : ℕ) :
    ∃ χ : Additive (ZMod (2 ^ (n + 3)))ˣ →+ AddCircle (1 : ℚ),
      χ (Additive.ofMul (ZMod.unitOfCoprime 5 (by
        exact Nat.Coprime.pow_right (n + 3) (by decide)))) =
          ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) ∧
      χ (Additive.ofMul (-1)) ≠ 0 ∧ Nat.card χ.ker ≤ 2 := by
  -- The value at five forces a cyclic image of order at least half the unit group.
  let u : (ZMod (2 ^ (n + 3)))ˣ :=
    ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right (n + 3) (by decide))
  have hu : addOrderOf (Additive.ofMul u) = 2 ^ (n + 1) := by
    rw [addOrderOf_ofMul_eq_orderOf, ← orderOf_units]
    exact ZMod.orderOf_five (n + 1)
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ : Additive (ZMod (2 ^ (n + 3)))ˣ →+ AddCircle (1 : ℚ),
      χ (Additive.ofMul u) = ((1 / addOrderOf (Additive.ofMul u) : ℚ) : AddCircle (1 : ℚ)) :=
    originalRationalCircle_exists_prescribed_character (Additive.ofMul u) (hu.trans_ne (by positivity))
  have hχ₀ : χ₀ (Additive.ofMul u) = ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) := by
    simpa only [hu, Nat.cast_pow, Nat.cast_ofNat] using hχ₀
  -- A character modulo four changes the value at -1 without changing the value at five.
  have hneg : addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) = 2 := by
    rw [addOrderOf_ofMul_eq_orderOf]
    exact orderOf_eq_prime (by simp) (by decide)
  obtain ⟨δ, hδ⟩ : ∃ δ : Additive (ZMod 4)ˣ →+ AddCircle (1 : ℚ),
      δ (Additive.ofMul (-1)) =
        ((1 / addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) : ℚ) : AddCircle (1 : ℚ)) :=
    originalRationalCircle_exists_prescribed_character (Additive.ofMul (-1 : (ZMod 4)ˣ)) (hneg.trans_ne (by decide))
  have hδ : δ (Additive.ofMul (-1)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    simpa only [hneg, Nat.cast_ofNat] using hδ
  have h4 : 4 ∣ 2 ^ (n + 3) := by
    exact_mod_cast (pow_dvd_pow 2 (show 2 ≤ n + 3 by omega))
  let ρ := ZMod.unitsMap h4
  have hρu : ρ u = 1 := by
    apply Units.ext
    simp only [ρ, ZMod.unitsMap_val, u, ZMod.coe_unitOfCoprime, Units.val_one]
    rw [ZMod.cast_natCast h4]
    decide
  have hρneg : ρ (-1) = -1 := by
    apply Units.ext
    simp only [ρ, ZMod.unitsMap_val, Units.val_neg, Units.val_one]
    rw [ZMod.cast_neg h4, ZMod.cast_one h4]
  let χ : Additive (ZMod (2 ^ (n + 3)))ˣ →+ AddCircle (1 : ℚ) :=
    if χ₀ (Additive.ofMul (-1)) = 0 then χ₀ + δ.comp ρ.toAdditive else χ₀
  have hχu : χ (Additive.ofMul u) = ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) := by
    simp only [χ]
    split_ifs <;> simp [hχ₀, hρu]
  have hχneg : χ (Additive.ofMul (-1)) ≠ 0 := by
    simp only [χ]
    split_ifs with h
    · simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply,
        toMul_ofMul, hρneg, h, zero_add, hδ]
      have hord := AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := 2) (by decide)
      norm_num only [Nat.cast_ofNat] at hord
      intro hz
      rw [hz, addOrderOf_zero] at hord
      omega
    · exact h
  -- The image-order bound and the kernel/image formula give the index-two bound.
  have hcard : Nat.card (Additive (ZMod (2 ^ (n + 3)))ˣ) = 2 * 2 ^ (n + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp [pow_succ, Nat.mul_comm]
  have hrange : 2 ^ (n + 1) ≤ Nat.card χ.range := by
    have hmem : χ (Additive.ofMul u) ∈ χ.range := ⟨_, rfl⟩
    have hdvd := χ.range.addOrderOf_dvd_natCard hmem
    have hord : addOrderOf ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) = 2 ^ (n + 1) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := 2 ^ (n + 1)) (by positivity)
    rw [hχu, hord] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  refine ⟨χ, hχu, hχneg, ?_⟩
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup χ.ker
  rw [hcard, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange χ).toEquiv] at hmul
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  nlinarith


end
end Dubon2026
