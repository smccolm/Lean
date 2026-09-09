import Tao2026.PartialSummation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Variation bounds for the reciprocal phase

The low-frequency branch of the pinned Proposition 1.12 proof uses that
`t ↦ N/t + M/t^j` has total variation `O(F)` on a dyadic interval, where
`F = |N|/X + |M|/X^j`.  This module proves the pointwise derivative estimate
and its mean-value consequence with explicit constants.
-/

open Set

namespace Tao2026

noncomputable section

/-- The reciprocal phase is differentiable at every positive point. -/
theorem differentiableAt_reciprocalPhase_of_pos
    (N M : ℝ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (reciprocalPhase N M j) t := by
  have hpowOne : ContDiffAt ℝ 1 (fun y : ℝ => y ^ (-1 : ℤ)) t := by
    exact ((analyticAt_id.zpow ht.ne').contDiffAt.of_le le_top)
  have hpowJ : ContDiffAt ℝ 1 (fun y : ℝ => y ^ (-(j : ℤ))) t := by
    exact ((analyticAt_id.zpow ht.ne').contDiffAt.of_le le_top)
  have htermOne : ContDiffAt ℝ 1 (fun y : ℝ => N * y ^ (-1 : ℤ)) t :=
    contDiffAt_const.mul hpowOne
  have htermJ : ContDiffAt ℝ 1 (fun y : ℝ => M * y ^ (-(j : ℤ))) t :=
    contDiffAt_const.mul hpowJ
  exact (htermOne.add htermJ).differentiableAt (by norm_num)

/-- On `[X,∞)`, the first derivative is bounded by
`(j+1) F / X`, with the source scale `F` explicit. -/
theorem abs_deriv_reciprocalPhase_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X t : ℝ}
    (hX : 0 < X) (hXt : X ≤ t) :
    |deriv (reciprocalPhase N M j) t| ≤
      (j + 1 : ℕ) * reciprocalPhaseScale N M j X / X := by
  have ht : 0 < t := hX.trans_le hXt
  have hraw := normalized_abs_iteratedDeriv_reciprocalPhase_le_multiplier_scale
    N M (j := j) (r := 1) hj hX hXt
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one,
    iteratedDeriv_one, Nat.cast_add] at hraw
  have hscale : 0 ≤ (j + 1 : ℕ) * reciprocalPhaseScale N M j X :=
    mul_nonneg (Nat.cast_nonneg _) (reciprocalPhaseScale_nonneg N M j hX)
  calc
    |deriv (reciprocalPhase N M j) t| ≤
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X) / t := by
      rw [le_div_iff₀ ht]
      simpa [add_comm, mul_comm] using hraw
    _ ≤ ((j + 1 : ℕ) * reciprocalPhaseScale N M j X) / X :=
      div_le_div_of_nonneg_left hscale hX hXt

/-- Explicit mean-value estimate for the phase on a positive dyadic
interval.  In particular its oscillation across an interval of length `L`
is at most `(j+1) F L/X`. -/
theorem abs_reciprocalPhase_sub_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X s t : ℝ}
    (hX : 0 < X) (hs : s ∈ Set.Icc X (2 * X))
    (ht : t ∈ Set.Icc X (2 * X)) :
    |reciprocalPhase N M j t - reciprocalPhase N M j s| ≤
      ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) * |t - s| := by
  have hdiff : ∀ x ∈ Set.Icc X (2 * X),
      DifferentiableAt ℝ (reciprocalPhase N M j) x := by
    intro x hx
    exact differentiableAt_reciprocalPhase_of_pos N M j (hX.trans_le hx.1)
  have hbound : ∀ x ∈ Set.Icc X (2 * X),
      ‖deriv (reciprocalPhase N M j) x‖ ≤
        (j + 1 : ℕ) * reciprocalPhaseScale N M j X / X := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact abs_deriv_reciprocalPhase_le N M hj hX hx.1
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc X (2 * X)) hs ht)

/-- The additive character inherits the reciprocal phase's pointwise
variation bound.  This is the coefficient estimate needed by finite Abel
summation in the low-frequency branch. -/
theorem norm_standardAdditiveCharacter_reciprocalPhase_sub_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X s t : ℝ}
    (hX : 0 < X) (hs : s ∈ Set.Icc X (2 * X))
    (ht : t ∈ Set.Icc X (2 * X)) :
    ‖standardAdditiveCharacter (reciprocalPhase N M j t) -
        standardAdditiveCharacter (reciprocalPhase N M j s)‖ ≤
      2 * Real.pi *
        (((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) * |t - s|) := by
  calc
    ‖standardAdditiveCharacter (reciprocalPhase N M j t) -
        standardAdditiveCharacter (reciprocalPhase N M j s)‖ ≤
        2 * Real.pi *
          |reciprocalPhase N M j t - reciprocalPhase N M j s| :=
      norm_standardAdditiveCharacter_sub_le _ _
    _ ≤ 2 * Real.pi *
        (((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) * |t - s|) := by
      exact mul_le_mul_of_nonneg_left
        (abs_reciprocalPhase_sub_le N M hj hX hs ht)
        (mul_nonneg (by positivity) Real.pi_pos.le)

/-- One integer step of the reciprocal-phase character on `[X,2X]` costs
at most `2π(j+1)F/X`. -/
theorem norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X) {n : ℕ}
    (hn : X ≤ n) (hnTop : (n + 1 : ℕ) ≤ 2 * X) :
    ‖standardAdditiveCharacter (reciprocalPhase N M j (n + 1)) -
        standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      2 * Real.pi * ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) := by
  have hn' : (n : ℝ) ∈ Set.Icc X (2 * X) := by
    constructor
    · exact hn
    · have hnLeSucc : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ n
      exact hnLeSucc.trans hnTop
  have hnSucc : ((n + 1 : ℕ) : ℝ) ∈ Set.Icc X (2 * X) := by
    constructor
    · exact hn.trans (by exact_mod_cast Nat.le_succ n)
    · exact hnTop
  simpa using
    (norm_standardAdditiveCharacter_reciprocalPhase_sub_le
      N M hj hX hn' hnSucc)

/-- Explicit finite total variation before the interval length is absorbed.
Every step in `[a,b-1)` lies in the dyadic phase range by the endpoint
hypotheses. -/
theorem sum_norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    {a b : ℕ} (hXa : X ≤ a) (hbTop : b ≤ 2 * X) :
    ∑ n ∈ Finset.Ico a (b - 1),
        ‖standardAdditiveCharacter (reciprocalPhase N M j (n + 1)) -
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ((Finset.Ico a (b - 1)).card : ℝ) *
        (2 * Real.pi * ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) := by
  calc
    ∑ n ∈ Finset.Ico a (b - 1),
        ‖standardAdditiveCharacter (reciprocalPhase N M j (n + 1)) -
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
        ∑ _n ∈ Finset.Ico a (b - 1),
          (2 * Real.pi * ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) := by
      apply Finset.sum_le_sum
      intro n hnMem
      apply norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le N M hj hX
      · exact hXa.trans (by exact_mod_cast (Finset.mem_Ico.mp hnMem).1)
      · have hnLt : n + 1 < b := by
          have hnBound := (Finset.mem_Ico.mp hnMem).2
          omega
        have hnLe : ((n + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast hnLt.le
        exact hnLe.trans hbTop
    _ = ((Finset.Ico a (b - 1)).card : ℝ) *
        (2 * Real.pi * ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) := by
      simp

/-- On a natural subinterval of `[X,2X]`, the total variation of the
reciprocal-phase character is at most `2π(j+1)F`. -/
theorem sum_norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le_scale
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    {a b : ℕ} (hab : a < b) (hXa : X ≤ a) (hbTop : b ≤ 2 * X) :
    ∑ n ∈ Finset.Ico a (b - 1),
        ‖standardAdditiveCharacter (reciprocalPhase N M j (n + 1)) -
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      2 * Real.pi * ((j + 1 : ℕ) * reciprocalPhaseScale N M j X) := by
  have hraw :=
    sum_norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le
      N M hj hX hXa hbTop
  have hcardNat : (Finset.Ico a (b - 1)).card ≤ b - a := by
    rw [Nat.card_Ico]
    omega
  have hba : ((b - a : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_sub hab.le]
    linarith
  have hcard : ((Finset.Ico a (b - 1)).card : ℝ) ≤ X := by
    have hcardCast : ((Finset.Ico a (b - 1)).card : ℝ) ≤ (b - a : ℕ) := by
      exact_mod_cast hcardNat
    exact hcardCast.trans hba
  have hcoefficient :
      0 ≤ 2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) Real.pi_pos.le)
      (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (reciprocalPhaseScale_nonneg N M j hX)) hX.le)
  calc
    ∑ n ∈ Finset.Ico a (b - 1),
        ‖standardAdditiveCharacter (reciprocalPhase N M j (n + 1)) -
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
        ((Finset.Ico a (b - 1)).card : ℝ) *
          (2 * Real.pi *
            ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) := hraw
    _ ≤ X * (2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) :=
      mul_le_mul_of_nonneg_right hcard hcoefficient
    _ = 2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X) := by
      field_simp [hX.ne']

/-- On the entire dyadic interval the phase oscillation is at most
`(j+1)F`, the precise scale invoked in the low-frequency PNT branch. -/
theorem abs_reciprocalPhase_sub_le_scale
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X s t : ℝ}
    (hX : 0 < X) (hs : s ∈ Set.Icc X (2 * X))
    (ht : t ∈ Set.Icc X (2 * X)) :
    |reciprocalPhase N M j t - reciprocalPhase N M j s| ≤
      (j + 1 : ℕ) * reciprocalPhaseScale N M j X := by
  have hdist : |t - s| ≤ X := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hcoef : 0 ≤ (j + 1 : ℕ) * reciprocalPhaseScale N M j X / X := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (reciprocalPhaseScale_nonneg N M j hX)) hX.le
  calc
    |reciprocalPhase N M j t - reciprocalPhase N M j s| ≤
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) * |t - s| :=
      abs_reciprocalPhase_sub_le N M hj hX hs ht
    _ ≤ ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X) * X :=
      mul_le_mul_of_nonneg_left hdist hcoef
    _ = (j + 1 : ℕ) * reciprocalPhaseScale N M j X := by
      field_simp [hX.ne']

end

end Tao2026
