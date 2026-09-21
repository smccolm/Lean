import TaoTrudgianYang2025.AtkinsonSignedPhaseSeries
import Mathlib.Algebra.BigOperators.Module

/-!
# Partial summation of the actual two signed main sums

Only the raw phases are conjugated. Each sign keeps its own actual weight.
The bound contains literal finite differences; their uniform analytic
variation estimate is a separate, still necessary obligation.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def atkinsonPhasePartialSum (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonPositivePhaseTerm T n

def atkinsonMainAbelBound (T G L : ℝ) (N : ℕ) : ℝ :=
  (‖atkinsonPositiveMainWeight T G L (N-1)‖+
    ‖atkinsonNegativeMainWeight T G L (N-1)‖)*‖atkinsonPhasePartialSum T N‖ +
  ∑ n ∈ Finset.range (N-1),
    (‖atkinsonPositiveMainWeight T G L (n+1)-atkinsonPositiveMainWeight T G L n‖+
      ‖atkinsonNegativeMainWeight T G L (n+1)-atkinsonNegativeMainWeight T G L n‖)*
        ‖atkinsonPhasePartialSum T (n+1)‖

theorem atkinsonNegativePhaseTerm_eq_conj (T : ℝ) (n : ℕ) :
    atkinsonNegativePhaseTerm T n = (starRingEnd ℂ) (atkinsonPositivePhaseTerm T n) := by
  unfold atkinsonNegativePhaseTerm atkinsonPositivePhaseTerm divisorWeight
  simp only [map_mul,map_pow,map_neg,map_one,map_natCast,← Complex.exp_conj,
    Complex.conj_ofReal,Complex.conj_I]
  congr 2
  ring

theorem atkinsonNegativePhaseSum_eq_conj (T : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, atkinsonNegativePhaseTerm T n) =
      (starRingEnd ℂ) (atkinsonPhasePartialSum T N) := by
  simp only [atkinsonPhasePartialSum,atkinsonNegativePhaseTerm_eq_conj,map_sum]

theorem norm_atkinsonNegativePhaseSum (T : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, atkinsonNegativePhaseTerm T n‖ =
      ‖atkinsonPhasePartialSum T N‖ := by
  rw [atkinsonNegativePhaseSum_eq_conj]
  exact Complex.norm_conj _

theorem norm_sum_mul_le_discrete_parts (w a : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n*a n‖ ≤
      ‖w (N-1)‖*‖∑ n ∈ Finset.range N, a n‖+
        ∑ n ∈ Finset.range (N-1),
          ‖w (n+1)-w n‖*‖∑ k ∈ Finset.range (n+1), a k‖ := by
  have he := Finset.sum_range_by_parts w a N
  simp only [smul_eq_mul] at he
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact add_le_add le_rfl ((norm_sum_le _ _).trans_eq (by simp only [norm_mul]))

theorem atkinsonMainAbelBound_nonneg (T G L : ℝ) (N : ℕ) :
    0 ≤ atkinsonMainAbelBound T G L N := by
  unfold atkinsonMainAbelBound
  positivity

theorem norm_atkinsonMainSums_le_abel (T G L : ℝ) (N : ℕ) :
    ‖atkinsonPositiveMainSum T G L N‖+‖atkinsonNegativeMainSum T G L N‖ ≤
      atkinsonMainAbelBound T G L N := by
  have hp := norm_sum_mul_le_discrete_parts (atkinsonPositiveMainWeight T G L)
    (atkinsonPositivePhaseTerm T) N
  have hm := norm_sum_mul_le_discrete_parts (atkinsonNegativeMainWeight T G L)
    (atkinsonNegativePhaseTerm T) N
  simp only [norm_atkinsonNegativePhaseSum] at hm
  change ‖atkinsonPositiveMainSum T G L N‖ ≤ _ at hp
  change ‖atkinsonNegativeMainSum T G L N‖ ≤ _ at hm
  apply (add_le_add hp hm).trans_eq
  unfold atkinsonMainAbelBound atkinsonPhasePartialSum
  simp only [add_mul,Finset.sum_add_distrib]
  ring

theorem norm_atkinsonStationaryLeadingSum_le_abel {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) :
    ‖atkinsonStationaryLeadingSum T G L‖ ≤
      2*atkinsonMainAbelBound T G L (atkinsonSourceCutoff T G L) := by
  apply (norm_atkinsonStationaryLeadingSum_le_signed hT hG hL hwidth).trans
  exact mul_le_mul_of_nonneg_left (norm_atkinsonMainSums_le_abel T G L _) (by norm_num)

end TaoTrudgianYang2025
