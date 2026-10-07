import Dubon2026.GammaFrequencySeparation

/-! # The literal degree-four Riesz Gamma symbol and its critical vertical lines -/

namespace Dubon2026

open Complex

noncomputable section

/-- The line on which the degree-four order-r Riesz Gamma symbol has amplitude exponent minus one half. -/
def gammaRieszLine (r : ℝ) : ℝ := 3 / 8 - r / 4

/-- The actual two-Gamma functional-equation ratio after the order-r Riesz denominator is cancelled. -/
def gammaRieszSymbol (k r : ℝ) (s : ℂ) : ℂ :=
  Gamma (1 - s) * Gamma ((k : ℂ) - s) /
    (Gamma (s + ((r + 1 : ℝ) : ℂ)) * Gamma (s + ((k - 1 : ℝ) : ℂ)))

/-- On any vertical line the actual Riesz symbol is exactly the product of the two reflected Gamma ratios. -/
theorem gammaRieszSymbol_vertical_eq (k r β t : ℝ) :
    gammaRieszSymbol k r (gammaVerticalPoint β t) =
      reflectedGammaRatio (1 - β) (β + r + 1) t * reflectedGammaRatio (k - β) (β + k - 1) t := by
  unfold gammaRieszSymbol reflectedGammaRatio gammaVerticalPoint
  rw [div_mul_div_comm]
  congr 3 <;> push_cast <;> ring

/-- Every true Gamma shift is positive on the critical Riesz lines for weights at least two and orders zero through two. -/
theorem gammaRiesz_shifts_pos {k r : ℝ} (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    0 < 1 - gammaRieszLine r ∧ 0 < gammaRieszLine r + r + 1 ∧
      0 < k - gammaRieszLine r ∧ 0 < gammaRieszLine r + k - 1 := by
  unfold gammaRieszLine
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The actual horizontal power is precisely minus one half on these lines, with no epsilon loss. -/
theorem gammaRiesz_power (k r : ℝ) :
    ((1 - gammaRieszLine r) - (gammaRieszLine r + r + 1)) +
      ((k - gammaRieszLine r) - (gammaRieszLine r + k - 1)) = -(1 / 2 : ℝ) := by
  unfold gammaRieszLine
  ring

/-- A single explicit height dominates every actual shift and the full frequency-approximation error. -/
theorem gammaRiesz_shifts_le {k r T : ℝ} (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hT : 21 + 2 * k ≤ T) :
    1 - gammaRieszLine r ≤ T ∧ gammaRieszLine r + r + 1 ≤ T ∧
      k - gammaRieszLine r ≤ T ∧ gammaRieszLine r + k - 1 ≤ T ∧
      16 + (1 - gammaRieszLine r) + (gammaRieszLine r + r + 1) +
        (k - gammaRieszLine r) + (gammaRieszLine r + k - 1) ≤ T := by
  unfold gammaRieszLine
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The real positive vertical power splits into its exact modulus and a linear unit phase. -/
theorem positive_cpow_vertical_eq {x : ℝ} (hx : 0 < x) (β t : ℝ) :
    (x : ℂ) ^ gammaVerticalPoint β t =
      (x ^ β : ℝ) * Complex.exp (I * ((Real.log x * t : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
  rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  simp only [gammaVerticalPoint, ofReal_mul]
  ring

end
end Dubon2026
