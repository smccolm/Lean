import GuthMaynard.Separated
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Bourgain's actual integer difference counts

This is the finite counting input of Bourgain (2000), equations (4.6) and
(4.21). The window is strict, all ordered pairs are retained, and the
pointwise bound uses two-unit separation. The finite support below is a
cover; a covered integer may still have count zero.
-/

open Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual number of ordered pairs with difference within one of an integer. -/
def bourgainDifferenceCount (W : Finset ℝ) (ℓ : ℤ) : ℕ :=
  ((W ×ˢ W).filter fun p => |p.1 - p.2 - (ℓ : ℝ)| < 1).card

/-- A finite cover of every nonzero difference count. -/
def bourgainDifferenceSupport (W : Finset ℝ) : Finset ℤ :=
  (W ×ˢ W).biUnion fun p => {⌊p.1 - p.2⌋, ⌊p.1 - p.2⌋ + 1}

/-- A strict unit neighborhood contains at most the two adjacent integers. -/
theorem bourgain_integer_near_difference {x : ℝ} {ℓ : ℤ}
    (h : |x - (ℓ : ℝ)| < 1) :
    ℓ = ⌊x⌋ ∨ ℓ = ⌊x⌋ + 1 := by
  have hb := abs_lt.mp h
  have hlow : ⌊x⌋ ≤ ℓ := (Int.floor_le_iff).mpr (by linarith)
  have hhigh : ℓ < ⌊x⌋ + 2 := by
    have hreal : (ℓ : ℝ) < (⌊x⌋ : ℝ) + 2 := by
      linarith [Int.lt_floor_add_one x]
    exact_mod_cast hreal
  omega

/-- Outside the finite cover there is no contributing ordered pair. -/
theorem bourgainDifferenceCount_eq_zero_of_not_mem
    (W : Finset ℝ) {ℓ : ℤ} (hℓ : ℓ ∉ bourgainDifferenceSupport W) :
    bourgainDifferenceCount W ℓ = 0 := by
  classical
  unfold bourgainDifferenceCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  apply hℓ
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp'.1, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    bourgain_integer_near_difference hp'.2

/-- The count is precisely a finite sum of its ordered-pair indicators. -/
theorem bourgainDifferenceCount_eq_sum (W : Finset ℝ) (ℓ : ℤ) :
    bourgainDifferenceCount W ℓ =
      ∑ p ∈ W ×ˢ W, if |p.1 - p.2 - (ℓ : ℝ)| < 1 then 1 else 0 := by
  classical
  simp only [bourgainDifferenceCount, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Counting first by pairs gives the sharp factor two, on any finite set
of integer bins. No separation hypothesis is needed here. -/
theorem bourgainDifferenceCount_sum_le (W : Finset ℝ) (D : Finset ℤ) :
    ∑ ℓ ∈ D, bourgainDifferenceCount W ℓ ≤ 2 * W.card ^ 2 := by
  classical
  simp_rw [bourgainDifferenceCount_eq_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _p ∈ W ×ˢ W, 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hsub : D.filter (fun ℓ : ℤ => |p.1-p.2-(ℓ : ℝ)| < 1) ⊆
          {⌊p.1-p.2⌋, ⌊p.1-p.2⌋+1} := by
        intro ℓ hℓ
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          bourgain_integer_near_difference (Finset.mem_filter.mp hℓ).2
      have hc := Finset.card_le_card hsub
      have htwo : ({⌊p.1-p.2⌋, ⌊p.1-p.2⌋+1} : Finset ℤ).card ≤ 2 := by
        exact (Finset.card_insert_le _ _).trans (by simp)
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hc.trans htwo
    _ = _ := by simp [pow_two, mul_comm]

/-- Two-unit separation makes projection to the first ordinate injective
on every strict difference bin. This includes the diagonal bin. -/
theorem bourgainDifferenceCount_le_card {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (ℓ : ℤ) :
    bourgainDifferenceCount W ℓ ≤ W.card := by
  classical
  unfold bourgainDifferenceCount
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpW := Finset.mem_product.mp hp'.1
    have hqW := Finset.mem_product.mp hq'.1
    apply Prod.ext hpq
    by_contra hne
    have hdist : 2 ≤ |p.2-q.2| := by
      simpa only [Real.dist_eq] using hsep p.2 hpW.2 q.2 hqW.2 hne
    have hb₁ := abs_lt.mp hp'.2
    have hb₂ := abs_lt.mp hq'.2
    have hlt : |p.2-q.2| < 2 := abs_lt.mpr (by constructor <;> linarith)
    linarith

/-- Bourgain's finite square-count estimate, with all multiplicities
computed from the actual ordinate set. -/
theorem bourgainDifferenceCount_sum_sq_le {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (D : Finset ℤ) :
    ∑ ℓ ∈ D, bourgainDifferenceCount W ℓ ^ 2 ≤ 2 * W.card ^ 3 := by
  calc
    _ ≤ ∑ ℓ ∈ D, W.card * bourgainDifferenceCount W ℓ := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      simpa only [pow_two] using
        Nat.mul_le_mul_right (bourgainDifferenceCount W ℓ)
          (bourgainDifferenceCount_le_card hsep ℓ)
    _ = W.card * ∑ ℓ ∈ D, bourgainDifferenceCount W ℓ := by rw [Finset.mul_sum]
    _ ≤ W.card * (2 * W.card ^ 2) :=
      Nat.mul_le_mul_left _ (bourgainDifferenceCount_sum_le W D)
    _ = _ := by ring

/-- Real-valued version used in weighted zeta moments. -/
theorem bourgainDifferenceCount_sum_sq_cast_le {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (D : Finset ℤ) :
    ∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ) ^ 2 ≤ 2 * (W.card : ℝ) ^ 3 := by
  exact_mod_cast bourgainDifferenceCount_sum_sq_le hsep D

/-- Cauchy--Schwarz with the actual multiplicities, not an independently
assumed weight bound. The test function may have either sign. -/
theorem bourgainDifferenceCount_weighted_sq_le {W : Finset ℝ}
    (hsep : IsSeparated 2 W) (D : Finset ℤ) (f : ℤ → ℝ) :
    (∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ) * f ℓ) ^ 2 ≤
      2 * (W.card : ℝ) ^ 3 * ∑ ℓ ∈ D, f ℓ ^ 2 := by
  exact (Finset.sum_mul_sq_le_sq_mul_sq D
    (fun ℓ => (bourgainDifferenceCount W ℓ : ℝ)) f).trans
      (mul_le_mul_of_nonneg_right (bourgainDifferenceCount_sum_sq_cast_le hsep D)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Every covered integer lies within one of the actual height range.
This is derived from the source ordinates, not a separate bin-range input. -/
theorem bourgainDifferenceSupport_bounds {W : Finset ℝ} {T : ℝ}
    (hbase : InBaseInterval T W) {ℓ : ℤ} (hℓ : ℓ ∈ bourgainDifferenceSupport W) :
    -T - 1 ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ T + 1 := by
  classical
  obtain ⟨p, hp, hchoice⟩ := Finset.mem_biUnion.mp hℓ
  have hpW := Finset.mem_product.mp hp
  have ht := hbase p.1 hpW.1
  have hu := hbase p.2 hpW.2
  have hfloor := Int.floor_le (p.1-p.2)
  have hceil := Int.lt_floor_add_one (p.1-p.2)
  rcases Finset.mem_insert.mp hchoice with rfl | hc
  · constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
  · rw [Finset.mem_singleton] at hc
    rw [hc]
    push_cast
    constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]

/-- Exact weighted double counting, before an analytic integrand is chosen. -/
theorem bourgainDifferenceCount_weighted_eq (W : Finset ℝ)
    (D : Finset ℤ) (g : ℤ → ℝ) :
    (∑ ℓ ∈ D, (bourgainDifferenceCount W ℓ : ℝ) * g ℓ) =
      ∑ p ∈ W ×ˢ W, ∑ ℓ ∈ D,
        if |p.1-p.2-(ℓ : ℝ)| < 1 then g ℓ else 0 := by
  classical
  simp_rw [bourgainDifferenceCount_eq_sum]
  push_cast
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]

end TaoTrudgianYang2025
