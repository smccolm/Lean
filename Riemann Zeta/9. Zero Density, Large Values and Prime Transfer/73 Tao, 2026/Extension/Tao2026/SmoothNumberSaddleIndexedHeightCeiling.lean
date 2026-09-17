import Tao2026.SmoothNumberSaddlePostTerminalTail

/-!
# The physical ceiling of the indexed root-shell method

An indexed shell can use the retained CEP/PNT alphabet only while its
iterated prime scale remains at least four.  That arithmetic requirement
forces the shell's physical upper height below one absolute constant,
independently of the index and of `y`.  Consequently an admissible indexed
terminal height cannot tend to infinity, even when its shell index does.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

/-- The absolute physical-height ceiling forced by survival of the terminal
iterated prime scale. -/
noncomputable def smoothSaddleIndexedAdmissibleHeightCeiling : ℝ :=
  3 * Real.pi / (2 * Real.log 4)

theorem smoothSaddleIndexedAdmissibleHeightCeiling_pos :
    0 < smoothSaddleIndexedAdmissibleHeightCeiling := by
  unfold smoothSaddleIndexedAdmissibleHeightCeiling
  positivity

/-- If indexed depth `k >= 1` retains a prime scale of at least four, its
physical endpoint is bounded by the absolute admissible-height ceiling. -/
theorem smoothSaddleIndexedOuterUpperHeight_le_admissibleHeightCeiling
    {k y : ℕ} (hk : 1 ≤ k)
    (hterminal : 4 ≤ smoothSaddleIteratedPrimeScale k y) :
    smoothSaddleIndexedOuterUpperHeight k y ≤
      smoothSaddleIndexedAdmissibleHeightCeiling := by
  have hpowNat : 4 ^ (2 ^ k) ≤ y :=
    (le_smoothSaddleIteratedPrimeScale_iff 4 k y).1 hterminal
  have hy4 : 4 ≤ y := by
    have h := four_le_iteratedPrimeScale_of_le (Nat.zero_le k) hterminal
    simpa [smoothSaddleIteratedPrimeScale] using h
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hpowReal : (4 : ℝ) ^ (2 ^ k) ≤ (y : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow := Real.log_le_log
    (by positivity : (0 : ℝ) < (4 : ℝ) ^ (2 ^ k)) hpowReal
  rw [Real.log_pow] at hlogPow
  have hdouble : 2 * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k := by
    calc
      2 * (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ (k - 1) * 2 := by ring
      _ = (2 : ℝ) ^ ((k - 1) + 1) := (pow_succ _ _).symm
      _ = (2 : ℝ) ^ k := by rw [Nat.sub_add_cancel hk]
  have hscale :
      2 * (2 : ℝ) ^ (k - 1) * Real.log 4 ≤ Real.log (y : ℝ) := by
    rw [hdouble]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlogPow
  unfold smoothSaddleIndexedOuterUpperHeight
    smoothSaddleIndexedAdmissibleHeightCeiling
  apply (div_le_div_iff₀ hlogy (mul_pos (by norm_num) hlog4)).2
  nlinarith [Real.pi_pos]

/-- A growing shell index whose terminal prime scale remains admissible has
eventually bounded physical height. -/
theorem eventually_indexedOuterUpperHeight_le_admissibleHeightCeiling
    {K y : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    (hterminal : ∀ᶠ n in atTop,
      4 ≤ smoothSaddleIteratedPrimeScale (K n) (y n)) :
    ∀ᶠ n in atTop,
      smoothSaddleIndexedOuterUpperHeight (K n) (y n) ≤
        smoothSaddleIndexedAdmissibleHeightCeiling := by
  filter_upwards [hK.eventually (eventually_ge_atTop 1), hterminal] with
      n hKn hscale
  exact smoothSaddleIndexedOuterUpperHeight_le_admissibleHeightCeiling
    hKn hscale

/-- Hence admissible indexed terminal heights cannot escape to infinity.
This is the formal obstruction to closing the post-terminal tail by merely
extending the iterated-root shell diagonal. -/
theorem not_tendsto_indexedOuterUpperHeight_atTop_of_admissible
    {K y : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    (hterminal : ∀ᶠ n in atTop,
      4 ≤ smoothSaddleIteratedPrimeScale (K n) (y n)) :
    ¬ Tendsto (fun n =>
      smoothSaddleIndexedOuterUpperHeight (K n) (y n)) atTop atTop := by
  intro hheight
  have hbounded :=
    eventually_indexedOuterUpperHeight_le_admissibleHeightCeiling
      hK hterminal
  have hlarge := hheight.eventually
    (eventually_gt_atTop smoothSaddleIndexedAdmissibleHeightCeiling)
  obtain ⟨n, hle, hlt⟩ := (hbounded.and hlarge).exists
  exact (not_lt_of_ge hle) hlt

end

end Tao2026
