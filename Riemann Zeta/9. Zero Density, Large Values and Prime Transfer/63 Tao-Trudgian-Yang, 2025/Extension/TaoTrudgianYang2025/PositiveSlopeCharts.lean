import TaoTrudgianYang2025.BetaSourceTaylorPhase

/-!
# A finite positive-slope grid

The grid depends only on a fixed positive mesh. Its half-open cells
partition the whole positive slope window, including its endpoints.
Each relevant cell lies strictly inside one multiplicative model chart.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

def positiveSlopeChartIndex (d v : ℝ) : ℕ := ⌊v/d⌋₊

def positiveSlopeChartIndices (d : ℝ) : Finset ℕ := Finset.Icc 4 ⌊2/d⌋₊

def positiveSlopeChartScale (d : ℝ) (j : ℕ) : ℝ := 3*(j : ℝ)*d/4

theorem positiveSlopeChartIndex_eq_iff {d v : ℝ} (hd : 0 < d)
    (hv : 0 ≤ v) (j : ℕ) :
    positiveSlopeChartIndex d v = j ↔
      (j : ℝ)*d ≤ v ∧ v < ((j : ℝ)+1)*d := by
  rw [positiveSlopeChartIndex,Nat.floor_eq_iff (div_nonneg hv hd.le)]
  exact and_congr (le_div_iff₀ hd) (div_lt_iff₀ hd)

theorem positiveSlopeChartIndex_mono {d : ℝ} (hd : 0 < d) :
    Monotone (positiveSlopeChartIndex d) := by
  intro v w hvw
  exact Nat.floor_mono (div_le_div_of_nonneg_right hvw hd.le)

theorem positiveSlopeChartIndex_mem {d v : ℝ} (hd : 0 < d)
    (hv : v ∈ Icc (4*d) 2) :
    positiveSlopeChartIndex d v ∈ positiveSlopeChartIndices d := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.le_floor ((le_div_iff₀ hd).mpr (by simpa using hv.1))
  · exact Nat.floor_mono (div_le_div_of_nonneg_right hv.2 hd.le)

theorem positiveSlopeChartScale_bounds {d : ℝ} {j : ℕ}
    (hd : 0 < d) (hj : j ∈ positiveSlopeChartIndices d) :
    0 < positiveSlopeChartScale d j ∧ positiveSlopeChartScale d j ≤ 3/2 := by
  have hjlow : (4 : ℝ) ≤ j := by
    exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjhigh : (j : ℝ)*d ≤ 2 := by
    exact (le_div_iff₀ hd).mp ((Nat.le_floor_iff (by positivity : 0 ≤ (2 : ℝ)/d)).mp
      (Finset.mem_Icc.mp hj).2)
  unfold positiveSlopeChartScale
  constructor
  · positivity
  · nlinarith

theorem positiveSlopeChart_coordinate {d v : ℝ} {j : ℕ}
    (hd : 0 < d) (hj : 4 ≤ j)
    (hv : (j : ℝ)*d ≤ v ∧ v < ((j : ℝ)+1)*d) :
    v/positiveSlopeChartScale d j ∈ Ioo (1 : ℝ) 2 := by
  have hjreal : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hjd : 0 < (j : ℝ)*d := mul_pos (by linarith) hd
  have hA : 0 < positiveSlopeChartScale d j := by
    unfold positiveSlopeChartScale
    positivity
  constructor
  · apply (one_lt_div hA).mpr
    unfold positiveSlopeChartScale
    nlinarith [hv.1]
  · apply (div_lt_iff₀ hA).mpr
    unfold positiveSlopeChartScale
    nlinarith [hv.2,mul_le_mul_of_nonneg_right hjreal hd.le]

end TaoTrudgianYang2025
