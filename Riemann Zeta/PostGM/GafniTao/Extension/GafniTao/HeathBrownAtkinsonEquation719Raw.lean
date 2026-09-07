import GafniTao.HeathBrownAtkinsonFirstDerivativeScale
import GafniTao.HeathBrownAtkinsonGramExplicit

/-!
# Raw two-branch form of Ivić (7.19)

The existing B-process estimate is simplified here in the dimensionless
curvature variable `x=(t-u)/Q`.  For `x<1` it gives the classical
`K*sqrt(x)+1/sqrt(x)` expression; for `x>=1` the trivial length bound is
stronger.  This is then combined with the first-derivative branch.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A Gram entry has the trivial bound given by the length of its exact
index interval. -/
theorem norm_heathBrownAtkinsonGram_le_card
    (K : ℕ) (t u : ℝ) :
    ‖heathBrownAtkinsonGram K t u‖ ≤ (K : ℝ) := by
  rw [heathBrownAtkinsonGram_eq_positiveDifference_range]
  simpa only [Finset.card_range] using
    norm_phase_sum_finset_le_card (Finset.range K)
      (heathBrownAtkinsonPositiveDifferenceNat t u (K + 1))

/-- Numerical square-root comparison used to simplify the B-process
endpoint width. -/
theorem five_inv_sqrt_div_twenty_le_inv_sqrt
    {x : ℝ} (hx : 0 < x) :
    1 / Real.sqrt (x / 20) ≤ 5 / Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hx20 : 0 < x / 20 := by positivity
  have hs20 : 0 < Real.sqrt (x / 20) := Real.sqrt_pos.2 hx20
  have hroot : Real.sqrt x / 5 ≤ Real.sqrt (x / 20) := by
    have hsqx := Real.sq_sqrt hx.le
    have hsq20 := Real.sq_sqrt hx20.le
    have hleft : 0 ≤ Real.sqrt x / 5 := by positivity
    nlinarith
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < Real.sqrt x / 5) hroot
  calc
    1 / Real.sqrt (x / 20) ≤ 1 / (Real.sqrt x / 5) := hinv
    _ = 5 / Real.sqrt x := by field_simp [hsx.ne']

/-- Explicit algebraic simplification of the literal B-process majorant
when its normalized curvature is at most one. -/
theorem heathBrownAtkinsonGramGapMajorant_le_raw_of_ratio_le_one
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t)
    (hratio : (t - u) / heathBrownAtkinsonTerminalScale u K ≤ 1) :
    heathBrownAtkinsonGramGapMajorant K t u ≤
      300 *
        ((K : ℝ) * Real.sqrt
            ((t - u) / heathBrownAtkinsonTerminalScale u K) +
          1 / Real.sqrt
            ((t - u) / heathBrownAtkinsonTerminalScale u K)) := by
  let x := (t - u) / heathBrownAtkinsonTerminalScale u K
  have hQ := heathBrownAtkinsonTerminalScale_pos (K := K) hu
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsxSq := Real.sq_sqrt hx.le
  have hsxOne : Real.sqrt x ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hratio
  have hxLeSqrt : x ≤ Real.sqrt x := by
    nlinarith
  have hinv20 := five_inv_sqrt_div_twenty_le_inv_sqrt hx
  have hK : 0 ≤ (K : ℝ) := by positivity
  have hInv : 0 < 1 / Real.sqrt x := by positivity
  have hfour : (4 : ℝ) ≤ 4 * (1 / Real.sqrt x) := by
    have : 1 ≤ 1 / Real.sqrt x := (le_div_iff₀ hsx).2 (by simpa using hsxOne)
    linarith
  have hnonnegLeft : 0 ≤ 4 * (K : ℝ) * x + 2 := by positivity
  have hfirst : 4 * (K : ℝ) * (t - u) /
      heathBrownAtkinsonTerminalScale u K = 4 * (K : ℝ) * x := by
    dsimp only [x]
    ring
  have htwenty : (t - u) /
      (20 * heathBrownAtkinsonTerminalScale u K) = x / 20 := by
    dsimp only [x]
    field_simp [hQ.ne']
  have hsecond : 10 / Real.sqrt (x / 20) + 2 ≤
      50 / Real.sqrt x + 2 := by
    calc
      10 / Real.sqrt (x / 20) + 2 ≤
          10 * (5 / Real.sqrt x) + 2 := by
        have hm := mul_le_mul_of_nonneg_left hinv20 (by norm_num : (0 : ℝ) ≤ 10)
        convert add_le_add_right hm 2 using 1 <;> ring
      _ = 50 / Real.sqrt x + 2 := by ring
  have hKdiff : 0 ≤ (K : ℝ) * (Real.sqrt x - x) :=
    mul_nonneg hK (sub_nonneg.mpr hxLeSqrt)
  have hKpart :
      200 * (K : ℝ) * Real.sqrt x + 8 * (K : ℝ) * x ≤
        208 * ((K : ℝ) * Real.sqrt x) := by
    nlinarith
  have hInvpart :
      100 / Real.sqrt x + 4 ≤ 104 * (1 / Real.sqrt x) := by
    calc
      100 / Real.sqrt x + 4 = 100 * (1 / Real.sqrt x) + 4 := by ring
      _ ≤ 100 * (1 / Real.sqrt x) + 4 * (1 / Real.sqrt x) := by
        linarith
      _ = 104 * (1 / Real.sqrt x) := by ring
  unfold heathBrownAtkinsonGramGapMajorant
  calc
    (4 * (K : ℝ) * (t - u) /
          heathBrownAtkinsonTerminalScale u K + 2) *
        (10 / Real.sqrt
          ((t - u) / (20 * heathBrownAtkinsonTerminalScale u K)) + 2) =
        (4 * (K : ℝ) * x + 2) *
          (10 / Real.sqrt (x / 20) + 2) := by
      rw [hfirst, htwenty]
    _ ≤ (4 * (K : ℝ) * x + 2) *
        (50 / Real.sqrt x + 2) :=
      mul_le_mul_of_nonneg_left hsecond hnonnegLeft
    _ = 200 * (K : ℝ) * Real.sqrt x +
          8 * (K : ℝ) * x + 100 / Real.sqrt x + 4 := by
      field_simp [hsx.ne']
      nlinarith [hsxSq]
    _ ≤ 208 * ((K : ℝ) * Real.sqrt x) +
          104 * (1 / Real.sqrt x) := by
      linarith [hKpart, hInvpart]
    _ ≤ 300 * ((K : ℝ) * Real.sqrt x +
          1 / Real.sqrt x) := by
      nlinarith [mul_nonneg hK hsx.le, hInv.le]

/-- The B-process or the trivial bound gives a uniform raw exponent-pair
majorant for every positive height gap. -/
theorem norm_heathBrownAtkinsonGram_le_raw_B
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      300 *
        ((K : ℝ) * Real.sqrt
            ((t - u) / heathBrownAtkinsonTerminalScale u K) +
          1 / Real.sqrt
            ((t - u) / heathBrownAtkinsonTerminalScale u K)) := by
  let x := (t - u) / heathBrownAtkinsonTerminalScale u K
  have hQ := heathBrownAtkinsonTerminalScale_pos (K := K) hu
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  by_cases hxOne : x ≤ 1
  · exact (norm_heathBrownAtkinsonGram_le_gapMajorant_of_lt
      hu htu hK hblock htUpper).trans
        (by
          exact heathBrownAtkinsonGramGapMajorant_le_raw_of_ratio_le_one
            (K := K) (t := t) (u := u) hu htu
            (by simpa only [x] using hxOne))
  · have hone : 1 ≤ Real.sqrt x := by
      rw [Real.one_le_sqrt]
      exact le_of_not_ge hxOne
    have hKnonneg : 0 ≤ (K : ℝ) := by positivity
    have hterm : (K : ℝ) ≤ (K : ℝ) * Real.sqrt x := by
      nlinarith [mul_nonneg hKnonneg (sub_nonneg.mpr hone)]
    have hinv : 0 ≤ 1 / Real.sqrt x := by positivity
    change ‖heathBrownAtkinsonGram K t u‖ ≤
      300 * ((K : ℝ) * Real.sqrt x + 1 / Real.sqrt x)
    calc
      ‖heathBrownAtkinsonGram K t u‖ ≤ (K : ℝ) :=
        norm_heathBrownAtkinsonGram_le_card K t u
      _ ≤ (K : ℝ) * Real.sqrt x + 1 / Real.sqrt x := by linarith
      _ ≤ 300 * ((K : ℝ) * Real.sqrt x + 1 / Real.sqrt x) := by
        have hsum : 0 ≤ (K : ℝ) * Real.sqrt x + 1 / Real.sqrt x := by positivity
        nlinarith


end

end GafniTao
