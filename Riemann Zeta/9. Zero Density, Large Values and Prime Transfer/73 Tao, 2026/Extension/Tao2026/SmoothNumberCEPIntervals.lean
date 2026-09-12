import Tao2026.SmoothNumberCEPRecurrence

/-!
# Canfield--Erdős--Pomerance prime intervals

This file encodes the exact prime bands at the start of the proof of CEP
Theorem 3.1. We use the reversed zero-based index `t = k - j`, so the source
interval becomes

`(x ^ ((1/u) * (1 - (t+1)/log(u)^3)),
  x ^ ((1/u) * (1 - t/log(u)^3))]`.

The reversed form makes adjacency and pairwise disjointness literal.
-/

open scoped BigOperators

namespace Tao2026

noncomputable section

open Finset

/-- A finite open--closed prime band inside the bounded-prime alphabet. -/
noncomputable def cepOpenClosedPrimeBand
    (y : ℕ) (lower upper : ℝ) : Finset (TaoBoundedPrime y) :=
  Finset.univ.filter fun p => lower < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ upper

theorem mem_cepOpenClosedPrimeBand_iff
    {y : ℕ} {lower upper : ℝ} {p : TaoBoundedPrime y} :
    p ∈ cepOpenClosedPrimeBand y lower upper ↔
      lower < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ upper := by
  simp [cepOpenClosedPrimeBand]

/-- Two open--closed bands are disjoint when the upper endpoint of the lower
band does not exceed the lower endpoint of the upper band. -/
theorem disjoint_cepOpenClosedPrimeBand_of_le
    {y : ℕ} {lower₁ upper₁ lower₂ upper₂ : ℝ}
    (hsep : upper₂ ≤ lower₁) :
    Disjoint (cepOpenClosedPrimeBand y lower₁ upper₁)
      (cepOpenClosedPrimeBand y lower₂ upper₂) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hp₁' := mem_cepOpenClosedPrimeBand_iff.mp hp₁
  have hp₂' := mem_cepOpenClosedPrimeBand_iff.mp hp₂
  linarith

/-- Lower exponent of the reversed zero-based CEP prime band. -/
def cepSourceBandLowerExponent (u : ℝ) (t : ℕ) : ℝ :=
  (1 / u) * (1 - ((t + 1 : ℕ) : ℝ) / Real.log u ^ 3)

/-- Upper exponent of the reversed zero-based CEP prime band. -/
def cepSourceBandUpperExponent (u : ℝ) (t : ℕ) : ℝ :=
  (1 / u) * (1 - (t : ℝ) / Real.log u ^ 3)

def cepSourceBandLower (x u : ℝ) (t : ℕ) : ℝ :=
  x ^ cepSourceBandLowerExponent u t

def cepSourceBandUpper (x u : ℝ) (t : ℕ) : ℝ :=
  x ^ cepSourceBandUpperExponent u t

/-- The exact source interval `I_j`, expressed with `t = k-j`. -/
noncomputable def cepSourcePrimeBand
    (x u : ℝ) (y t : ℕ) : Finset (TaoBoundedPrime y) :=
  cepOpenClosedPrimeBand y (cepSourceBandLower x u t)
    (cepSourceBandUpper x u t)

theorem mem_cepSourcePrimeBand_iff
    {x u : ℝ} {y t : ℕ} {p : TaoBoundedPrime y} :
    p ∈ cepSourcePrimeBand x u y t ↔
      cepSourceBandLower x u t < ((p : ℕ) : ℝ) ∧
        ((p : ℕ) : ℝ) ≤ cepSourceBandUpper x u t := by
  exact mem_cepOpenClosedPrimeBand_iff

/-- Later reversed bands lie below earlier ones, with adjacent endpoints
meeting exactly. -/
theorem cepSourceBandUpperExponent_le_lowerExponent
    {u : ℝ} (hu : 1 < u) {t s : ℕ} (hts : t < s) :
    cepSourceBandUpperExponent u s ≤ cepSourceBandLowerExponent u t := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hden : 0 < Real.log u ^ 3 := pow_pos hlog 3
  have hcast : (((t + 1 : ℕ) : ℝ)) ≤ (s : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hts)
  have hdiv : (((t + 1 : ℕ) : ℝ)) / Real.log u ^ 3 ≤
      (s : ℝ) / Real.log u ^ 3 :=
    by gcongr
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Lower endpoints decrease as the reversed band index increases. -/
theorem cepSourceBandLowerExponent_anti
    {u : ℝ} (hu : 1 < u) {t s : ℕ} (hts : t ≤ s) :
    cepSourceBandLowerExponent u s ≤ cepSourceBandLowerExponent u t := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hcast : (((t + 1 : ℕ) : ℝ)) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hts 1
  have hdiv : (((t + 1 : ℕ) : ℝ)) / Real.log u ^ 3 ≤
      ((s + 1 : ℕ) : ℝ) / Real.log u ^ 3 := by
    gcongr
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem cepSourceBandLowerExponent_le_upperExponent
    {u : ℝ} (hu : 1 < u) (t : ℕ) :
    cepSourceBandLowerExponent u t ≤ cepSourceBandUpperExponent u t := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hcast : (t : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ t
  have hdiv : (t : ℝ) / Real.log u ^ 3 ≤
      ((t + 1 : ℕ) : ℝ) / Real.log u ^ 3 := by
    gcongr
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem cepSourceBandUpperExponent_le_one_div
    {u : ℝ} (hu : 1 < u) (t : ℕ) :
    cepSourceBandUpperExponent u t ≤ 1 / u := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  calc
    cepSourceBandUpperExponent u t =
        (1 / u) * (1 - (t : ℝ) / Real.log u ^ 3) := rfl
    _ ≤ (1 / u) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · have : 0 ≤ (t : ℝ) / Real.log u ^ 3 := by positivity
        linarith
      · positivity
    _ = 1 / u := mul_one _

theorem cepSourceBandLower_anti
    {x u : ℝ} (hx : 1 ≤ x) (hu : 1 < u) {t s : ℕ} (hts : t ≤ s) :
    cepSourceBandLower x u s ≤ cepSourceBandLower x u t := by
  apply Real.rpow_le_rpow_of_exponent_le hx
  exact cepSourceBandLowerExponent_anti hu hts

theorem cepSourceBandLower_le_upper
    {x u : ℝ} (hx : 1 ≤ x) (hu : 1 < u) (t : ℕ) :
    cepSourceBandLower x u t ≤ cepSourceBandUpper x u t := by
  apply Real.rpow_le_rpow_of_exponent_le hx
  exact cepSourceBandLowerExponent_le_upperExponent hu t

theorem cepSourceBandUpper_le_globalCutoff
    {x u : ℝ} (hx : 1 ≤ x) (hu : 1 < u) (t : ℕ) :
    cepSourceBandUpper x u t ≤ x ^ (1 / u) := by
  apply Real.rpow_le_rpow_of_exponent_le hx
  exact cepSourceBandUpperExponent_le_one_div hu t

theorem cepSourceBandUpper_le_lower
    {x u : ℝ} (hx : 1 ≤ x) (hu : 1 < u) {t s : ℕ} (hts : t < s) :
    cepSourceBandUpper x u s ≤ cepSourceBandLower x u t := by
  apply Real.rpow_le_rpow_of_exponent_le hx
  exact cepSourceBandUpperExponent_le_lowerExponent hu hts

/-- The exact CEP source bands are pairwise disjoint. -/
theorem disjoint_cepSourcePrimeBand
    {x u : ℝ} {y : ℕ} (hx : 1 ≤ x) (hu : 1 < u)
    {t s : ℕ} (hts : t ≠ s) :
    Disjoint (cepSourcePrimeBand x u y t) (cepSourcePrimeBand x u y s) := by
  rcases lt_or_gt_of_ne hts with hlt | hgt
  · exact disjoint_cepOpenClosedPrimeBand_of_le
      (cepSourceBandUpper_le_lower hx hu hlt)
  · exact (disjoint_cepOpenClosedPrimeBand_of_le
      (cepSourceBandUpper_le_lower hx hu hgt)).symm

/-- The source order `j=1,...,k`, represented as the zero-based range, uses
the reversed band `t=k-1-j`. -/
noncomputable def cepSourcePrimeBandAt
    (x u : ℝ) (y k j : ℕ) : Finset (TaoBoundedPrime y) :=
  cepSourcePrimeBand x u y (k - 1 - j)

theorem disjoint_cepSourcePrimeBandAt
    {x u : ℝ} {y k i j : ℕ} (hx : 1 ≤ x) (hu : 1 < u)
    (hi : i ∈ Finset.range k) (hj : j ∈ Finset.range k) (hij : i ≠ j) :
    Disjoint (cepSourcePrimeBandAt x u y k i)
      (cepSourcePrimeBandAt x u y k j) := by
  apply disjoint_cepSourcePrimeBand hx hu
  intro heq
  have hi' : i < k := Finset.mem_range.mp hi
  have hj' : j < k := Finset.mem_range.mp hj
  omega

/-- Any natural cutoff below a band's real lower endpoint is strictly below
every prime in that band. -/
theorem nat_lt_prime_of_le_cepSourceBandLower
    {x u : ℝ} {y w t : ℕ} {p : TaoBoundedPrime y}
    (hw : (w : ℝ) ≤ cepSourceBandLower x u t)
    (hp : p ∈ cepSourcePrimeBand x u y t) : w < (p : ℕ) := by
  have hp' := (mem_cepSourcePrimeBand_iff.mp hp).1
  exact_mod_cast (lt_of_le_of_lt hw hp')

end

end Tao2026
