import Tao2026.IntervalMultiples
import Tao2026.TypicalBadIntervals

/-!
# First finite reductions for non-typical bad intervals

This module begins the proof of Proposition 6.5.  It closes the purely
combinatorial part of condition (ii): every short normalized interval that
contains a multiple of a large square is covered by an explicit finite union
of short neighborhoods, and that union has the exact reciprocal-square sum
bound used before taking asymptotics.
-/

namespace Tao2026

/-- Natural points at distance at most `L` from `j`, with truncation at zero. -/
def closedNatNeighborhood (j L : ℕ) : Finset ℕ :=
  Finset.Icc (j - L) (j + L)

theorem card_closedNatNeighborhood_le (j L : ℕ) :
    (closedNatNeighborhood j L).card ≤ 2 * L + 1 := by
  simp only [closedNatNeighborhood, Nat.card_Icc]
  omega

/-- Explicit exceptional set for the large-square-multiple branch of
Proposition 6.5.  The outer range may stop at `2x`: a positive `d` with
`d² ∣ j ≤ 2x` necessarily satisfies `d ≤ 2x`. -/
def largeSquareMultipleNeighborhood (x squareThreshold L : ℕ) : Finset ℕ :=
  (Finset.Icc squareThreshold (2 * x)).biUnion fun d =>
    (intervalMultiples 0 (2 * x) (d ^ 2)).biUnion fun j =>
      closedNatNeighborhood j L

/-- A short comparable-scale interval failing typicality condition (ii) is
contained in the explicit large-square exceptional set. -/
theorem consecutiveInterval_subset_largeSquareMultipleNeighborhood
    {x squareThreshold L N H : ℕ} (hthreshold : 0 < squareThreshold)
    (hshort : H ≤ L) (hscale : N + H ≤ 2 * x)
    (hfail : ¬AvoidsSquareMultiplesAtLeast N H squareThreshold) :
    consecutiveInterval N H ⊆
      largeSquareMultipleNeighborhood x squareThreshold L := by
  simp only [AvoidsSquareMultiplesAtLeast] at hfail
  push Not at hfail
  obtain ⟨j, hj, d, hdLower, hdSq⟩ := hfail
  have hjBounds := Finset.mem_Ioc.mp hj
  have hjTwoX : j ≤ 2 * x := hjBounds.2.trans hscale
  have hdPos : 0 < d := hthreshold.trans_le hdLower
  have hdSqLeJ : d ^ 2 ≤ j := Nat.le_of_dvd (by omega) hdSq
  have hdLeSq : d ≤ d ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right d hdPos
  have hdTwoX : d ≤ 2 * x := hdLeSq.trans (hdSqLeJ.trans hjTwoX)
  have hdMem : d ∈ Finset.Icc squareThreshold (2 * x) :=
    Finset.mem_Icc.mpr ⟨hdLower, hdTwoX⟩
  have hjMultiple : j ∈ intervalMultiples 0 (2 * x) (d ^ 2) :=
    mem_intervalMultiples.mpr ⟨by omega, by simpa using hjTwoX, hdSq⟩
  intro n hn
  have hnBounds := Finset.mem_Ioc.mp hn
  have hnNear : n ∈ closedNatNeighborhood j L := by
    simp only [closedNatNeighborhood, Finset.mem_Icc]
    omega
  exact Finset.mem_biUnion.mpr
    ⟨d, hdMem, Finset.mem_biUnion.mpr ⟨j, hjMultiple, hnNear⟩⟩

/-- Exact counting reduction behind
`x log^20(x) * ∑_{d≥z³} d⁻²`.  All analytic weakening is postponed: this
finite theorem loses only the harmless neighborhood factor `2L+1`. -/
theorem card_largeSquareMultipleNeighborhood_le
    {x squareThreshold L : ℕ} :
    (largeSquareMultipleNeighborhood x squareThreshold L).card ≤
      ∑ d ∈ Finset.Icc squareThreshold (2 * x),
        (2 * L + 1) * (2 * x / d ^ 2) := by
  classical
  calc
    (largeSquareMultipleNeighborhood x squareThreshold L).card
        ≤ ∑ d ∈ Finset.Icc squareThreshold (2 * x),
            ((intervalMultiples 0 (2 * x) (d ^ 2)).biUnion fun j =>
              closedNatNeighborhood j L).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.Icc squareThreshold (2 * x),
          ∑ _j ∈ intervalMultiples 0 (2 * x) (d ^ 2), (2 * L + 1) := by
          apply Finset.sum_le_sum
          intro d hd
          exact Finset.card_biUnion_le.trans (by
            apply Finset.sum_le_sum
            intro _j _hj
            exact card_closedNatNeighborhood_le _ L)
    _ = ∑ d ∈ Finset.Icc squareThreshold (2 * x),
          (2 * L + 1) * (intervalMultiples 0 (2 * x) (d ^ 2)).card := by
          apply Finset.sum_congr rfl
          intro d hd
          simp [Nat.mul_comm]
    _ ≤ ∑ d ∈ Finset.Icc squareThreshold (2 * x),
          (2 * L + 1) * (2 * x / d ^ 2) := by
          exact le_of_eq (by simp only [card_intervalMultiples_zero])

/-- The elementary telescoping comparison
`1/d² ≤ 1/(d-1) - 1/d` for `d ≥ 2`. -/
theorem one_div_nat_sq_le_telescope (d : ℕ) (hd : 2 ≤ d) :
    (1 : ℝ) / (d : ℝ) ^ 2 ≤
      1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdmR : (0 : ℝ) < (d - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < d - 1)
  norm_num [Nat.cast_sub (by omega : 1 ≤ d)] at hdmR ⊢
  have hdmR' : (0 : ℝ) < (d : ℝ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (by omega : 1 < d)
  have hrhs :
      ((d : ℝ) - 1)⁻¹ - (d : ℝ)⁻¹ =
        (((d : ℝ) - 1) * d)⁻¹ := by
    field_simp
    ring
  rw [hrhs]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (mul_pos hdmR' hdR) (by nlinarith :
      ((d : ℝ) - 1) * d ≤ d ^ 2))

/-- Sharp finite telescoping remainder for a reciprocal-square interval. -/
theorem sum_Icc_one_div_nat_sq_le_sub (D : ℕ) (hD : 2 ≤ D) :
    ∀ U : ℕ, D ≤ U →
      (∑ d ∈ Finset.Icc D U, (1 : ℝ) / (d : ℝ) ^ 2) ≤
        1 / ((D - 1 : ℕ) : ℝ) - 1 / (U : ℝ) := by
  intro U
  induction U with
  | zero => omega
  | succ U ih =>
      intro hDU
      by_cases hEq : D = U + 1
      · subst D
        simpa using one_div_nat_sq_le_telescope (U + 1) hD
      · have hDU' : D ≤ U := by omega
        rw [Finset.sum_Icc_succ_top hDU]
        calc
          (∑ d ∈ Finset.Icc D U, (1 : ℝ) / (d : ℝ) ^ 2) +
              1 / ((U + 1 : ℕ) : ℝ) ^ 2
              ≤ (1 / ((D - 1 : ℕ) : ℝ) - 1 / (U : ℝ)) +
                  (1 / (((U + 1) - 1 : ℕ) : ℝ) -
                    1 / ((U + 1 : ℕ) : ℝ)) :=
                add_le_add (ih hDU')
                  (one_div_nat_sq_le_telescope (U + 1) (by omega))
          _ = 1 / ((D - 1 : ℕ) : ℝ) - 1 / ((U + 1 : ℕ) : ℝ) := by
                rw [Nat.add_sub_cancel]
                ring

/-- Uniform reciprocal-square tail bound, valid even when the finite interval
is empty. -/
theorem sum_Icc_one_div_nat_sq_le {D U : ℕ} (hD : 2 ≤ D) :
    (∑ d ∈ Finset.Icc D U, (1 : ℝ) / (d : ℝ) ^ 2) ≤
      1 / ((D - 1 : ℕ) : ℝ) := by
  by_cases hDU : D ≤ U
  · exact (sum_Icc_one_div_nat_sq_le_sub D hD U hDU).trans
      (sub_le_self _ (by positivity))
  · have hempty : Finset.Icc D U = ∅ := by
      ext d
      simp only [Finset.mem_Icc]
      simp
      omega
    rw [hempty]
    simp

/-- Closed real-valued form of the large-square exceptional-set estimate.
This completes the reciprocal-square tail calculation in the condition-(ii)
branch of Proposition 6.5, prior to substituting the source's choices of `L`
and `D`. -/
theorem card_largeSquareMultipleNeighborhood_cast_le
    {x squareThreshold L : ℕ} (hthreshold : 2 ≤ squareThreshold) :
    ((largeSquareMultipleNeighborhood x squareThreshold L).card : ℝ) ≤
      ((2 * L + 1 : ℕ) : ℝ) * (2 * x : ℕ) /
        ((squareThreshold - 1 : ℕ) : ℝ) := by
  have hcard := card_largeSquareMultipleNeighborhood_le
    (x := x) (squareThreshold := squareThreshold) (L := L)
  calc
    ((largeSquareMultipleNeighborhood x squareThreshold L).card : ℝ)
        ≤ ((∑ d ∈ Finset.Icc squareThreshold (2 * x),
            (2 * L + 1) * (2 * x / d ^ 2) : ℕ) : ℝ) := by
          exact_mod_cast hcard
    _ = ∑ d ∈ Finset.Icc squareThreshold (2 * x),
          (((2 * L + 1) * (2 * x / d ^ 2) : ℕ) : ℝ) := by
          push_cast
          rfl
    _ ≤ ∑ d ∈ Finset.Icc squareThreshold (2 * x),
          ((2 * L + 1 : ℕ) : ℝ) *
            ((2 * x : ℕ) : ℝ) / (d : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Nat.cast_mul]
          rw [mul_div_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hcast := Nat.cast_div_le (α := ℝ) (m := 2 * x) (n := d ^ 2)
          norm_num at hcast ⊢
          exact hcast
    _ = ((2 * L + 1 : ℕ) : ℝ) * ((2 * x : ℕ) : ℝ) *
          (∑ d ∈ Finset.Icc squareThreshold (2 * x),
            (1 : ℝ) / (d : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
    _ ≤ ((2 * L + 1 : ℕ) : ℝ) * ((2 * x : ℕ) : ℝ) *
          (1 / ((squareThreshold - 1 : ℕ) : ℝ)) := by
          gcongr
          exact sum_Icc_one_div_nat_sq_le hthreshold
    _ = ((2 * L + 1 : ℕ) : ℝ) * (2 * x : ℕ) /
          ((squareThreshold - 1 : ℕ) : ℝ) := by ring

/-- Specialization to a typicality failure: once condition (i) holds, failure
of condition (ii) places the entire interval in the preceding exceptional
set. -/
theorem IsScaleNormalizedBadInterval.largeSquare_failure_subset
    {x lengthCutoff squareThreshold N H : ℕ}
    (hscale : IsScaleNormalizedBadInterval x N H)
    (hthreshold : 0 < squareThreshold) (hshort : H < lengthCutoff)
    (hfail : ¬AvoidsSquareMultiplesAtLeast N H squareThreshold) :
    consecutiveInterval N H ⊆
      largeSquareMultipleNeighborhood x squareThreshold lengthCutoff := by
  obtain ⟨_p₀, _k, _m, _hnorm, _hleft, hright⟩ := hscale
  exact consecutiveInterval_subset_largeSquareMultipleNeighborhood
    hthreshold (Nat.le_of_lt hshort) hright hfail

end Tao2026
