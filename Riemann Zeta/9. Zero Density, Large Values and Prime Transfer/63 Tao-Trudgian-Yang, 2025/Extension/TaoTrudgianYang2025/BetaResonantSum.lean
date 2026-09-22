import TaoTrudgianYang2025.BetaLogCoherence

/-! Explicit genuine logarithmic sums of square-root size. The scale,
integer summation endpoints and eventual beta witness are all linked. -/

noncomputable section

open Expdb RiemannZeta.GuthMaynard
open Filter Topology

namespace TaoTrudgianYang2025

def betaResonantScale (m : ℕ) : ℕ := 16*(m+1)^2

theorem betaResonantScale_cast (m : ℕ) :
    (betaResonantScale m : ℝ) = 16*((m : ℝ)+1)^2 := by
  simp [betaResonantScale]

theorem betaResonantScale_one_le (m : ℕ) :
    1 ≤ (betaResonantScale m : ℝ) := by
  rw [betaResonantScale_cast]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem betaResonantScale_index_le (m : ℕ) :
    (m : ℝ) ≤ (betaResonantScale m : ℝ) := by
  rw [betaResonantScale_cast]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem betaResonantScale_sqrt (m : ℕ) :
    Real.sqrt (betaResonantScale m) = 4*((m : ℝ)+1) := by
  rw [betaResonantScale_cast,show 16*((m : ℝ)+1)^2 = (4*((m : ℝ)+1))^2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem betaResonantScale_small (m j : ℕ) (hj : j ≤ m) :
    (j : ℝ)^2/(betaResonantScale m : ℝ) ≤ 1/16 := by
  have hpos : 0 < (betaResonantScale m : ℝ) :=
    lt_of_lt_of_le zero_lt_one (betaResonantScale_one_le m)
  apply (div_le_iff₀ hpos).2
  rw [betaResonantScale_cast]
  have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j),(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem betaResonantScale_tendsto :
    Tendsto (fun m => (betaResonantScale m : ℝ)) atTop atTop :=
  tendsto_atTop_mono betaResonantScale_index_le tendsto_natCast_atTop_atTop

theorem norm_logPhase_resonant_sum_lower (m : ℕ) :
    Real.sqrt (betaResonantScale m)/8 ≤
      ‖exponentialSumAt Real.log (betaResonantScale m) (betaResonantScale m)
        (betaResonantScale m) (betaResonantScale m+m)‖ := by
  let N := betaResonantScale m
  have hN : 0 < (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one (betaResonantScale_one_le m)
  have hsum : exponentialSumAt Real.log N N N (N+m) =
      ∑ j ∈ Finset.range (m+1), oscillatory Real.log N N ((N : ℝ)+j) := by
    unfold exponentialSumAt
    rw [sum_Icc_eq_shifted_range _ N (N+m) (by omega)]
    simp only [Nat.add_sub_cancel_left,Nat.cast_add]
  rw [hsum,betaResonantScale_sqrt]
  have hre : ((m : ℝ)+1)/2 ≤
      (∑ j ∈ Finset.range (m+1), oscillatory Real.log N N ((N : ℝ)+j)).re := by
    have hpoint (j : ℕ) (hj : j ∈ Finset.range (m+1)) :
        (1 : ℝ)/2 ≤ (oscillatory Real.log N N ((N : ℝ)+j)).re :=
      oscillatory_log_re_ge_half hN j (betaResonantScale_small m j (by
        have := Finset.mem_range.mp hj
        omega))
    have hs := Finset.sum_le_sum hpoint
    simpa [← Complex.re_sum] using hs
  have hn := Complex.re_le_norm
    (∑ j ∈ Finset.range (m+1), oscillatory Real.log N N ((N : ℝ)+j))
  linarith

end TaoTrudgianYang2025
