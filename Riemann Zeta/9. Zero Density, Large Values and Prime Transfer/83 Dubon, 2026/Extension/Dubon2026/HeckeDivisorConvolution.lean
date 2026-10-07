/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Selected divisor reindexing arguments adapt FourierHecke.lean at
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
The arithmetic is generalized to an explicit completely multiplicative weight.
-/
import Dubon2026.HeckePrimeLinear
import Mathlib.Data.Finset.NatDivisors

/-! # Divisor convolution for the actual Hecke coefficient transform -/

namespace Dubon2026

open Finset
open scoped Pointwise

noncomputable section

/-- The exact classical Hecke divisor weight, including vanishing at bad factors. -/
def heckeDivisorWeight (Q : ℕ) (k : ℤ) : ℕ →* ℂ where
  toFun d := if Nat.Coprime d Q then (d : ℂ) ^ (k - 1) else 0
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.coprime_mul_iff_left]
    split_ifs <;> simp_all [Nat.cast_mul, mul_zpow]

/-- The literal gcd-divisor transform with an explicit multiplicative arithmetic weight. -/
def weightedDivisorTransform (w : ℕ →* ℂ) (n : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ (m.gcd n).divisors, w d * a (m * n / (d * d))

/-- The actual classical coefficient formula is the gcd-divisor transform at every positive index. -/
theorem classicalHeckeCoefficient_eq_weighted (Q : ℕ) (k : ℤ) {n : ℕ} (hn : n ≠ 0)
    (a : ℕ → ℂ) (m : ℕ) :
    classicalHeckeCoefficient Q k n a m = weightedDivisorTransform (heckeDivisorWeight Q k) n a m := by
  have hg0 : m.gcd n ≠ 0 := by
    intro hz
    have hd := Nat.gcd_dvd_right m n
    rw [hz, zero_dvd_iff] at hd
    exact hn hd
  have hg := Nat.divisors_subset_of_dvd hn (Nat.gcd_dvd_right m n)
  unfold classicalHeckeCoefficient weightedDivisorTransform
  calc
    _ = ∑ d ∈ (m.gcd n).divisors, if Nat.Coprime d Q ∧ d ∣ m then
        (d : ℂ) ^ (k - 1) * a ((n / d) * (m / d)) else 0 := by
      symm
      apply Finset.sum_subset hg
      intro d hd hnot
      have hdm : ¬d ∣ m := fun h => hnot (Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd h (Nat.dvd_of_mem_divisors hd), hg0⟩)
      simp [hdm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdm := (Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left m n)
      have hdn := (Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right m n)
      have hquot : (n / d) * (m / d) = m * n / (d * d) := by
        rw [Nat.mul_div_mul_comm hdm hdn, mul_comm]
      by_cases hc : Nat.Coprime d Q <;> simp [heckeDivisorWeight, hc, hdm, hquot]

private theorem gcd_quot_sq_eq {m a b d₁ : ℕ} (hab : Nat.Coprime a b) (hd₁m : d₁ ∣ m)
    (hd₁a : d₁ ∣ a) : (m * a / (d₁ * d₁)).gcd b = m.gcd b := by
  rw [Nat.mul_div_mul_comm hd₁m hd₁a,
    Nat.Coprime.gcd_mul_right_cancel (m / d₁) (hab.coprime_dvd_left (Nat.div_dvd_of_dvd hd₁a))]
  conv_rhs => rw [show m = m / d₁ * d₁ from (Nat.div_mul_cancel hd₁m).symm]
  rw [Nat.Coprime.gcd_mul_right_cancel (m / d₁) (hab.coprime_dvd_left hd₁a)]

private theorem div_sq_product {m a b d₁ d₂ : ℕ} (hd₁ : d₁ * d₁ ∣ m * a) :
    m * (a * b) / (d₁ * d₂ * (d₁ * d₂)) = m * a / (d₁ * d₁) * b / (d₂ * d₂) := by
  rw [show d₁ * d₂ * (d₁ * d₂) = d₁ * d₁ * (d₂ * d₂) by ring,
    show m * (a * b) = m * a * b by ring, ← Nat.div_div_eq_div_mul]
  congr 1
  exact Nat.mul_div_right_comm hd₁ b

private theorem mul_injOn_divisors_coprime {m a b : ℕ} (hab : Nat.Coprime a b) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 * p.2)
      (↑((m.gcd a).divisors ×ˢ (m.gcd b).divisors)) := by
  intro ⟨d₁, d₂⟩ hd ⟨e₁, e₂⟩ he hmul
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hd he
  have hmul' : d₁ * d₂ = e₁ * e₂ := hmul
  have heq1 : d₁ = e₁ := Nat.dvd_antisymm
    (((hab.coprime_dvd_left
        ((Nat.dvd_of_mem_divisors hd.1).trans (Nat.gcd_dvd_right m a))).coprime_dvd_right
        ((Nat.dvd_of_mem_divisors he.2).trans (Nat.gcd_dvd_right m b))).dvd_of_dvd_mul_right
      (hmul' ▸ dvd_mul_right d₁ d₂))
    (((hab.coprime_dvd_left
        ((Nat.dvd_of_mem_divisors he.1).trans (Nat.gcd_dvd_right m a))).coprime_dvd_right
        ((Nat.dvd_of_mem_divisors hd.2).trans (Nat.gcd_dvd_right m b))).dvd_of_dvd_mul_right
      (hmul'.symm ▸ dvd_mul_right e₁ e₂))
  exact Prod.ext heq1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mem_divisors hd.1) (heq1 ▸ hmul'))


/-- Coprime index multiplication becomes composition of the actual divisor transforms. -/
theorem weightedDivisorTransform_coprime (w : ℕ →* ℂ) (c : ℕ → ℂ)
    (m a b : ℕ) (hab : Nat.Coprime a b) :
    weightedDivisorTransform w (a * b) c m =
      weightedDivisorTransform w a (weightedDivisorTransform w b c) m := by
  unfold weightedDivisorTransform
  rw [hab.gcd_mul m, Nat.divisors_mul,
    show (m.gcd a).divisors * (m.gcd b).divisors =
      Finset.image (fun p : ℕ × ℕ => p.1 * p.2)
        ((m.gcd a).divisors ×ˢ (m.gcd b).divisors) by
      ext d
      simp only [Finset.mem_mul, Finset.mem_image, Finset.mem_product]
      exact ⟨fun ⟨x, hx, y, hy, h⟩ => ⟨(x, y), ⟨hx, hy⟩, h⟩,
        fun ⟨⟨x, y⟩, ⟨hx, hy⟩, h⟩ => ⟨x, hx, y, hy, h⟩⟩,
    Finset.sum_image (fun _ ha _ hb h => mul_injOn_divisors_coprime hab ha hb h),
    Finset.sum_product]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  have hd₁m : d₁ ∣ m := (Nat.dvd_of_mem_divisors hd₁).trans (Nat.gcd_dvd_left m a)
  have hd₁a : d₁ ∣ a := (Nat.dvd_of_mem_divisors hd₁).trans (Nat.gcd_dvd_right m a)
  rw [gcd_quot_sq_eq hab hd₁m hd₁a, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d₂ _
  rw [map_mul, div_sq_product (Nat.mul_dvd_mul hd₁m hd₁a), mul_assoc]

/-- Coprime-index composition for the literal classical Fourier transform. -/
theorem classicalHeckeCoefficient_coprime_comp (Q : ℕ) (k : ℤ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) (c : ℕ → ℂ) (m : ℕ) :
    classicalHeckeCoefficient Q k (a * b) c m =
      classicalHeckeCoefficient Q k a (classicalHeckeCoefficient Q k b c) m := by
  rw [classicalHeckeCoefficient_eq_weighted Q k (mul_ne_zero ha hb),
    classicalHeckeCoefficient_eq_weighted Q k ha]
  rw [funext (classicalHeckeCoefficient_eq_weighted Q k hb c)]
  exact weightedDivisorTransform_coprime _ c m a b hab

end
end Dubon2026
