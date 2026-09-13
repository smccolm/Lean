import Tao2026.BadIntervalProposition65
import GafniTao.CountableDiagonal

/-!
# Slowly varying cutoffs for Proposition 6.5

This module replaces the concrete `9/10` anatomy cutoff by a countable
family approaching exponent one.  For the row indexed by `n`, write
`d = n + 10`.  The source anatomy cutoff is `z^(1-2/d)`, while the smooth
prime cover is allowed the slightly wider ambient endpoint `z^(1-1/d)`.
The intervening exponent grid has width `1/(2d^2)`, small enough that every
cell strictly below exponent one retains a positive `z`-saving.
-/

namespace Tao2026

open Filter Topology

noncomputable section

/-- Denominator used in the `n`th fixed row of the cutoff diagonal. -/
def taoSlowCutoffDenominator (n : ℕ) : ℕ := n + 10

/-- The lower anatomy exponent in row `n`: `1 - 2/(n+10)`. -/
noncomputable def taoSlowLowerExponent (n : ℕ) : ℝ :=
  1 - 2 / (taoSlowCutoffDenominator n : ℝ)

/-- A source-to-`2x` slack endpoint, still strictly below one. -/
noncomputable def taoSlowAmbientUpperExponent (n : ℕ) : ℝ :=
  1 - 1 / (taoSlowCutoffDenominator n : ℝ)

/-- The upper distinguished-prime exponent in row `n`: `1 + 2/(n+10)`. -/
noncomputable def taoSlowUpperExponent (n : ℕ) : ℝ :=
  1 + 2 / (taoSlowCutoffDenominator n : ℝ)

/-- A source-to-`2x` slack endpoint below the upper source exponent. -/
noncomputable def taoSlowAmbientLowerExponent (n : ℕ) : ℝ :=
  1 + 1 / (taoSlowCutoffDenominator n : ℝ)

/-- Grid size making `1-1/d` an exact grid endpoint. -/
def taoSlowGridSize (n : ℕ) : ℕ :=
  3 * taoSlowCutoffDenominator n ^ 2

/-- Number of grid cells between exponent `1/2` and `1-1/d`. -/
def taoSlowGridStop (n : ℕ) : ℕ :=
  taoSlowCutoffDenominator n * (taoSlowCutoffDenominator n - 2)

/-- First grid index at the upper slack exponent `1+1/d`. -/
def taoSlowHighGridStart (n : ℕ) : ℕ :=
  taoSlowCutoffDenominator n * (taoSlowCutoffDenominator n + 2)

theorem ten_le_taoSlowCutoffDenominator (n : ℕ) :
    10 ≤ taoSlowCutoffDenominator n := by
  simp [taoSlowCutoffDenominator]

theorem taoSlowCutoffDenominator_pos (n : ℕ) :
    0 < taoSlowCutoffDenominator n := by
  unfold taoSlowCutoffDenominator
  omega

theorem taoSlowGridSize_pos (n : ℕ) : 0 < taoSlowGridSize n := by
  unfold taoSlowGridSize
  exact Nat.mul_pos (by norm_num) (pow_pos (taoSlowCutoffDenominator_pos n) 2)

theorem taoSlowGridStop_pos (n : ℕ) : 0 < taoSlowGridStop n := by
  have hd := ten_le_taoSlowCutoffDenominator n
  unfold taoSlowGridStop
  exact Nat.mul_pos (taoSlowCutoffDenominator_pos n) (by omega)

theorem taoSlowLowerExponent_pos (n : ℕ) :
    0 < taoSlowLowerExponent n := by
  have hd : (10 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  rw [taoSlowLowerExponent]
  apply sub_pos.mpr
  rw [div_lt_one hdPos]
  linarith

theorem taoSlowLowerExponent_lt_ambient (n : ℕ) :
    taoSlowLowerExponent n < taoSlowAmbientUpperExponent n := by
  have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  rw [taoSlowLowerExponent, taoSlowAmbientUpperExponent]
  have : 1 / (taoSlowCutoffDenominator n : ℝ) <
      2 / (taoSlowCutoffDenominator n : ℝ) := by
    exact div_lt_div_of_pos_right (by norm_num) hdPos
  linarith

theorem taoSlowAmbientUpperExponent_lt_one (n : ℕ) :
    taoSlowAmbientUpperExponent n < 1 := by
  rw [taoSlowAmbientUpperExponent]
  have hden : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  have : (0 : ℝ) < 1 / (taoSlowCutoffDenominator n : ℝ) := one_div_pos.mpr hden
  linarith

theorem one_lt_taoSlowAmbientLowerExponent (n : ℕ) :
    1 < taoSlowAmbientLowerExponent n := by
  rw [taoSlowAmbientLowerExponent]
  have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  have : (0 : ℝ) < 1 / (taoSlowCutoffDenominator n : ℝ) := one_div_pos.mpr hd
  linarith

theorem taoSlowAmbientLowerExponent_lt_upper (n : ℕ) :
    taoSlowAmbientLowerExponent n < taoSlowUpperExponent n := by
  have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
    exact_mod_cast taoSlowCutoffDenominator_pos n
  rw [taoSlowAmbientLowerExponent, taoSlowUpperExponent]
  have : 1 / (taoSlowCutoffDenominator n : ℝ) <
      2 / (taoSlowCutoffDenominator n : ℝ) :=
    div_lt_div_of_pos_right (by norm_num) hd
  linarith

theorem taoSlowUpperExponent_lt_three (n : ℕ) :
    taoSlowUpperExponent n < 3 := by
  have hd : (10 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by positivity
  rw [taoSlowUpperExponent]
  have : 2 / (taoSlowCutoffDenominator n : ℝ) ≤ 1 / 5 := by
    rw [div_le_iff₀ hdPos]
    nlinarith
  linarith

/-- The chosen stopping index lands exactly at the slack endpoint
`1-1/d`. -/
theorem taoOneTermGridExponent_slowGridStop (n : ℕ) :
    taoOneTermGridExponent (taoSlowGridSize n) (taoSlowGridStop n) =
      taoSlowAmbientUpperExponent n := by
  let d := taoSlowCutoffDenominator n
  have hd : 2 ≤ d := by
    dsimp only [d]
    exact (ten_le_taoSlowCutoffDenominator n).trans' (by norm_num)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  change 1 / 2 + 3 * (d * (d - 2) : ℕ) / (2 * (3 * d ^ 2 : ℕ)) =
    1 - 1 / (d : ℝ)
  push_cast [Nat.cast_sub hd]
  field_simp [hdR]
  ring

/-- The upper moving-grid start lands exactly at exponent `1+1/d`. -/
theorem taoOneTermGridExponent_slowHighGridStart (n : ℕ) :
    taoOneTermGridExponent (taoSlowGridSize n) (taoSlowHighGridStart n) =
      taoSlowAmbientLowerExponent n := by
  let d := taoSlowCutoffDenominator n
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast (taoSlowCutoffDenominator_pos n).ne'
  change 1 / 2 + 3 * (d * (d + 2) : ℕ) / (2 * (3 * d ^ 2 : ℕ)) =
    1 + 1 / (d : ℝ)
  push_cast
  field_simp [hdR]
  ring

theorem taoSlowHighGridStart_lt_gridSize (n : ℕ) :
    taoSlowHighGridStart n < taoSlowGridSize n := by
  have hd := ten_le_taoSlowCutoffDenominator n
  unfold taoSlowHighGridStart taoSlowGridSize
  nlinarith

/-- Every retained moving-grid cell stays far enough below exponent one
to retain a uniform (for this fixed row) margin over exponent two. -/
theorem two_add_slowGridMargin_le
    {n k : ℕ} (hk : k ∈ Finset.range (taoSlowGridStop n)) :
    2 + 1 / (4 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
      taoOneTermGridExponent (taoSlowGridSize n) k +
        1 / taoOneTermGridExponent (taoSlowGridSize n) (k + 1) := by
  let d : ℕ := taoSlowCutoffDenominator n
  let K : ℕ := taoSlowGridSize n
  let a : ℝ := taoOneTermGridExponent K k
  let b : ℝ := taoOneTermGridExponent K (k + 1)
  have hd : 10 ≤ d := by
    simpa only [d] using ten_le_taoSlowCutoffDenominator n
  have hdPos : (0 : ℝ) < d := by positivity
  have hKPos : 0 < K := by
    simpa only [K] using taoSlowGridSize_pos n
  have hstep : b = a + 1 / (2 * (d : ℝ) ^ 2) := by
    have hdiff := taoOneTermGridExponent_succ_sub
      (K := K) (k := k) hKPos
    have hK : (K : ℝ) = 3 * (d : ℝ) ^ 2 := by
      simp only [K, d, taoSlowGridSize, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_pow]
    dsimp only [a, b]
    rw [hK] at hdiff
    have hcalc : 3 / (2 * (3 * (d : ℝ) ^ 2)) =
        1 / (2 * (d : ℝ) ^ 2) := by
      field_simp
    linarith
  have hkStop : k + 1 ≤ taoSlowGridStop n := by
    simpa only [Finset.mem_range] using hk
  have hbUpper : b ≤ 1 - 1 / (d : ℝ) := by
    have hmono := taoOneTermGridExponent_mono hKPos hkStop
    rw [taoOneTermGridExponent_slowGridStop n] at hmono
    simpa only [b, d, taoSlowAmbientUpperExponent] using hmono
  have haHalf : (1 / 2 : ℝ) ≤ a := by
    dsimp only [a, taoOneTermGridExponent]
    exact le_add_of_nonneg_right (by positivity)
  have hbPos : 0 < b := by
    rw [hstep]
    positivity
  have hbOne : b ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / d := by positivity
    linarith
  have hdistance : 1 / (d : ℝ) ≤ 1 - b := by
    linarith
  have hdistanceSq : 1 / (d : ℝ) ^ 2 ≤ (1 - b) ^ 2 := by
    have hu : 0 ≤ 1 / (d : ℝ) := by positivity
    have hv : 0 ≤ 1 - b := sub_nonneg.mpr hbOne
    have hsq := mul_self_le_mul_self hu hdistance
    calc
      1 / (d : ℝ) ^ 2 = (1 / (d : ℝ)) * (1 / (d : ℝ)) := by
        field_simp
      _ ≤ (1 - b) * (1 - b) := hsq
      _ = (1 - b) ^ 2 := by ring
  have hsmall :
      (1 / (2 * (d : ℝ) ^ 2) + 1 / (4 * (d : ℝ) ^ 2)) * b ≤
        (1 - b) ^ 2 := by
    have hleft :
        (1 / (2 * (d : ℝ) ^ 2) + 1 / (4 * (d : ℝ) ^ 2)) * b ≤
          1 / (d : ℝ) ^ 2 := by
      have hcoeffNonneg : 0 ≤
          1 / (2 * (d : ℝ) ^ 2) + 1 / (4 * (d : ℝ) ^ 2) := by
        positivity
      calc
        (1 / (2 * (d : ℝ) ^ 2) + 1 / (4 * (d : ℝ) ^ 2)) * b ≤
            (1 / (2 * (d : ℝ) ^ 2) + 1 / (4 * (d : ℝ) ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left hbOne hcoeffNonneg
        _ ≤ 1 / (d : ℝ) ^ 2 := by
          have hdSqPos : (0 : ℝ) < (d : ℝ) ^ 2 := sq_pos_of_pos hdPos
          rw [mul_one]
          field_simp
          nlinarith
    exact hleft.trans hdistanceSq
  have hmul :
      (2 + 1 / (4 * (d : ℝ) ^ 2) - a) * b ≤ 1 := by
    rw [hstep] at hsmall
    nlinarith
  have hdiv : 2 + 1 / (4 * (d : ℝ) ^ 2) - a ≤ 1 / b :=
    (le_div_iff₀ hbPos).2 hmul
  simpa only [a, b, d] using (show
    2 + 1 / (4 * (d : ℝ) ^ 2) ≤ a + 1 / b by linarith)

/-- The symmetric moving grid above exponent one has the same row-wise
positive margin. -/
theorem two_add_slowHighGridMargin_le
    {n k : ℕ}
    (hk : k ∈ Finset.Ico (taoSlowHighGridStart n) (taoSlowGridSize n)) :
    2 + 1 / (4 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
      taoOneTermGridExponent (taoSlowGridSize n) k +
        1 / taoOneTermGridExponent (taoSlowGridSize n) (k + 1) := by
  let d : ℕ := taoSlowCutoffDenominator n
  let K : ℕ := taoSlowGridSize n
  let a : ℝ := taoOneTermGridExponent K k
  let b : ℝ := taoOneTermGridExponent K (k + 1)
  have hd : 10 ≤ d := by
    simpa only [d] using ten_le_taoSlowCutoffDenominator n
  have hdPos : (0 : ℝ) < d := by positivity
  have hKPos : 0 < K := by simpa only [K] using taoSlowGridSize_pos n
  have hstep : b = a + 1 / (2 * (d : ℝ) ^ 2) := by
    have hdiff := taoOneTermGridExponent_succ_sub
      (K := K) (k := k) hKPos
    have hK : (K : ℝ) = 3 * (d : ℝ) ^ 2 := by
      simp only [K, d, taoSlowGridSize, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_pow]
    dsimp only [a, b]
    rw [hK] at hdiff
    have hcalc : 3 / (2 * (3 * (d : ℝ) ^ 2)) =
        1 / (2 * (d : ℝ) ^ 2) := by field_simp
    linarith
  have haLower : 1 + 1 / (d : ℝ) ≤ a := by
    have hmono := taoOneTermGridExponent_mono hKPos
      (Finset.mem_Ico.mp hk).1
    rw [taoOneTermGridExponent_slowHighGridStart n] at hmono
    simpa only [a, d, taoSlowAmbientLowerExponent] using hmono
  have hkSucc : k + 1 ≤ K := by
    have := (Finset.mem_Ico.mp hk).2
    omega
  have hbUpper : b ≤ 2 := by
    have hmono := taoOneTermGridExponent_mono hKPos hkSucc
    rw [taoOneTermGridExponent_self hKPos] at hmono
    simpa only [b] using hmono
  have haOne : 1 ≤ a := by
    have : (0 : ℝ) ≤ 1 / d := by positivity
    linarith
  have haTwo : a ≤ 2 := by
    rw [hstep] at hbUpper
    linarith [show (0 : ℝ) < 1 / (2 * (d : ℝ) ^ 2) by positivity]
  have hbPos : 0 < b := by
    have hstepPos : (0 : ℝ) < 1 / (2 * (d : ℝ) ^ 2) := by positivity
    rw [hstep]
    linarith
  have hdistance : 1 / (d : ℝ) ≤ a - 1 := by linarith
  have hdistanceSq : 1 / (d : ℝ) ^ 2 ≤ (a - 1) ^ 2 := by
    have hu : 0 ≤ 1 / (d : ℝ) := by positivity
    have hv : 0 ≤ a - 1 := sub_nonneg.mpr haOne
    have hsq := mul_self_le_mul_self hu hdistance
    calc
      1 / (d : ℝ) ^ 2 = (1 / (d : ℝ)) * (1 / (d : ℝ)) := by field_simp
      _ ≤ (a - 1) * (a - 1) := hsq
      _ = (a - 1) ^ 2 := by ring
  let h : ℝ := 1 / (2 * (d : ℝ) ^ 2)
  let c : ℝ := 1 / (4 * (d : ℝ) ^ 2)
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcost : h * (2 - a) ≤ h := by
    exact mul_le_of_le_one_right hh (by linarith)
  have hcB : c * b ≤ 2 * c := by
    nlinarith
  have hsum : h + 2 * c = 1 / (d : ℝ) ^ 2 := by
    dsimp only [h, c]
    ring
  have hmul : (2 + c - a) * b ≤ 1 := by
    have hstep' : b = a + h := by simpa only [h] using hstep
    nlinarith [sq_nonneg (a - 1)]
  have hdiv : 2 + c - a ≤ 1 / b := (le_div_iff₀ hbPos).2 hmul
  simpa only [a, b, c, d] using
    (show 2 + c ≤ a + 1 / b by linarith)

/-! ## The moving smooth-prime band below the anatomy cutoff -/

/-- The moving grid cells from exponent `1/2` to `1-1/d`. -/
def taoSlowGridIndices (n : ℕ) : Finset ℕ :=
  Finset.range (taoSlowGridStop n)

/-- Prime union over the moving grid cells at ambient scale `X`. -/
noncomputable def taoSlowGridPrimeUnion (n X : ℕ) : Finset ℕ :=
  (taoSlowGridIndices n).biUnion fun k =>
    taoOneTermExponentPrimeBand
      (taoOneTermGridExponent (taoSlowGridSize n) k)
      (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X

/-- Expanded ambient cover for the source band below the moving anatomy
cutoff.  The fixed `39/100` endpoint supplies dilation slack at the bottom. -/
noncomputable def taoSlowAmbientSmoothPrimeRange (n X : ℕ) : Finset ℕ :=
  taoOneTermExponentPrimeBand (39 / 100 : ℝ) (1 / 2 : ℝ) X ∪
    taoSlowGridPrimeUnion n X

/-- Literal source-scale smooth-prime band between the fixed small-prime
cutoff and the moving anatomy cutoff. -/
noncomputable def taoSlowSourceSmoothPrimeRange (n x : ℕ) : Finset ℕ :=
  taoOneTermExponentPrimeBand (2 / 5 : ℝ) (taoSlowLowerExponent n) x

/-- Each moving grid cell retains half of the arithmetic margin after the
fixed-band smooth-number error. -/
theorem eventually_sum_psiNat_slowGridBand_le
    {n k : ℕ} (hk : k ∈ taoSlowGridIndices n) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent (taoSlowGridSize n) k)
          (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (X : ℝ) / (taoZ X) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  have heps : (0 : ℝ) <
      1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) := by
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  filter_upwards [eventually_sum_psiNat_gridPrimeBand_le
      (K := taoSlowGridSize n) (k := k) (taoSlowGridSize_pos n) heps,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      X hband hz
  have hmargin := two_add_slowGridMargin_le
    (n := n) (k := k) (by simpa only [taoSlowGridIndices] using hk)
  have hdouble :
      1 / (4 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
        2 * (1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
    ring
  rw [hdouble] at hmargin
  have hexponent :
      2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
        taoOneTermGridExponent (taoSlowGridSize n) k +
          1 / taoOneTermGridExponent (taoSlowGridSize n) (k + 1) -
            1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) := by
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hz hexponent
  exact hband.trans (div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (taoZ_pos X) _) hpow)

/-- The cell estimate holds simultaneously over the finite moving grid. -/
theorem eventually_forall_sum_psiNat_slowGridBand_le (n : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ k ∈ taoSlowGridIndices n,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent (taoSlowGridSize n) k)
          (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (X : ℝ) / (taoZ X) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  rw [Filter.eventually_all_finset]
  intro k hk
  exact eventually_sum_psiNat_slowGridBand_le hk

/-- The fixed initial cell also satisfies the row-dependent moving margin. -/
theorem eventually_sum_psiNat_slowInitialBand_le (n : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (39 / 100 : ℝ) (1 / 2 : ℝ) X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (X : ℝ) / (taoZ X) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  filter_upwards [eventually_sum_psiNat_thirtyNineHundredths_to_half_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      X hinitial hz
  have hd : (10 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hmargin : 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
      3 / 1000 := by
    have hdPos : (0 : ℝ) < taoSlowCutoffDenominator n := by positivity
    have hdSq : (100 : ℝ) ≤ (taoSlowCutoffDenominator n : ℝ) ^ 2 := by nlinarith
    have hden : (0 : ℝ) < 8 * (taoSlowCutoffDenominator n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hz (by linarith :
      2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤ 2 + 3 / 1000)
  exact hinitial.trans (div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (taoZ_pos X) _) hpow)

/-- Summing the initial cell and every moving grid cell costs exactly the
fixed row-dependent number of bands. -/
theorem eventually_sum_psiNat_slowAmbientSmoothPrimeRange_le (n : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ taoSlowAmbientSmoothPrimeRange n X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        ((taoSlowGridStop n : ℝ) + 1) *
          ((X : ℝ) / (taoZ X) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
  filter_upwards [eventually_sum_psiNat_slowInitialBand_le n,
    eventually_forall_sum_psiNat_slowGridBand_le n] with X hinitial hbands
  let T : ℝ := (X : ℝ) / (taoZ X) ^
    (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))
  let f : ℕ → ℝ := fun p => (psiNat (X / p ^ 2) p : ℝ)
  have hgrid : (∑ p ∈ taoSlowGridPrimeUnion n X, f p) ≤
      (taoSlowGridStop n : ℝ) * T := by
    calc
      (∑ p ∈ taoSlowGridPrimeUnion n X, f p) ≤
          ∑ k ∈ taoSlowGridIndices n,
            ∑ p ∈ taoOneTermExponentPrimeBand
              (taoOneTermGridExponent (taoSlowGridSize n) k)
              (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X,
              f p := by
        exact sum_biUnion_le_sum_of_nonneg _ _ f (fun _ => by positivity)
      _ ≤ ∑ _k ∈ taoSlowGridIndices n, T := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [T, f] using hbands k hk
      _ = (taoSlowGridStop n : ℝ) * T := by
        simp [taoSlowGridIndices]
  calc
    (∑ p ∈ taoSlowAmbientSmoothPrimeRange n X,
        (psiNat (X / p ^ 2) p : ℝ)) ≤
        (∑ p ∈ taoOneTermExponentPrimeBand
          (39 / 100 : ℝ) (1 / 2 : ℝ) X, f p) +
          ∑ p ∈ taoSlowGridPrimeUnion n X, f p := by
      exact sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)
    _ ≤ T + (taoSlowGridStop n : ℝ) * T := by
      exact add_le_add (by simpa only [T, f] using hinitial) hgrid
    _ = ((taoSlowGridStop n : ℝ) + 1) * T := by ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- The literal source band embeds into its slackened moving-grid cover at
the exact cofactor scale `2x`. -/
theorem eventually_taoSlowSourceSmoothPrimeRange_subset (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowSourceSmoothPrimeRange n x ⊆
        taoSlowAmbientSmoothPrimeRange n (2 * x) := by
  filter_upwards [eventually_exponentCutoff_two_mul_le_of_lt
      (α := (39 / 100 : ℝ)) (β := (2 / 5 : ℝ)) (by norm_num) (by norm_num),
    eventually_exponentCutoff_le_two_mul_of_le
      (α := taoSlowLowerExponent n) (β := taoSlowAmbientUpperExponent n)
      (taoSlowLowerExponent_pos n).le
      (taoSlowLowerExponent_lt_ambient n).le] with x hlower hupper
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpBaseData := Finset.mem_filter.mp hpData.1
  have hpRange := Finset.mem_Icc.mp hpBaseData.1
  have hpSq : p * p ≤ 2 * x := by
    have hpSqX : p * p ≤ x := Nat.le_sqrt.mp hpRange.2
    omega
  have hpBase : p ∈ (Finset.Icc 2 (2 * x).sqrt).filter Nat.Prime := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpRange.1, Nat.le_sqrt.mpr hpSq⟩, hpBaseData.2⟩
  have hpExpanded : p ∈ taoOneTermExponentPrimeBand
      (39 / 100 : ℝ) (taoSlowAmbientUpperExponent n) (2 * x) :=
    Finset.mem_filter.mpr
      ⟨hpBase, lt_of_le_of_lt hlower hpData.2.1,
        hpData.2.2.trans hupper⟩
  rw [taoSlowAmbientSmoothPrimeRange]
  by_cases hpHalf : p ≤ taoOneTermExponentCutoff (1 / 2 : ℝ) (2 * x)
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨hpBase, (Finset.mem_filter.mp hpExpanded).2.1, hpHalf⟩
  · apply Finset.mem_union_right
    rw [taoSlowGridPrimeUnion]
    have hpGridBand : p ∈ taoOneTermExponentPrimeBand
        (taoOneTermGridExponent (taoSlowGridSize n) 0)
        (taoOneTermGridExponent (taoSlowGridSize n) (taoSlowGridStop n))
        (2 * x) := by
      rw [taoOneTermGridExponent_zero,
        taoOneTermGridExponent_slowGridStop n]
      exact Finset.mem_filter.mpr
        ⟨hpBase, Nat.lt_of_not_ge hpHalf,
          (Finset.mem_filter.mp hpExpanded).2.2⟩
    have hcovered := exponentPrimeBand_gridEndpoints_subset_biUnion
      (K := taoSlowGridSize n) (lo := 0) (hi := taoSlowGridStop n)
      (X := 2 * x) (taoSlowGridStop_pos n) hpGridBand
    rw [Finset.mem_biUnion] at hcovered ⊢
    obtain ⟨k, hk, hpk⟩ := hcovered
    exact ⟨k, by simpa only [taoSlowGridIndices, Finset.mem_range] using
      (Finset.mem_Ico.mp hk).2, hpk⟩

/-- The actual short normalized interval union over the ambient moving range,
before absorbing its fixed row-dependent combinatorial cost. -/
theorem eventually_card_taoSlowAmbientSmoothPrimeFailureUnion_raw (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowAmbientSmoothPrimeRange n (2 * x))).card : ℝ) ≤
        4 * (taoTypicalLengthCutoff x : ℝ) *
          (((taoSlowGridStop n : ℝ) + 1) *
            ((2 * x : ℕ) / (taoZ (2 * x)) ^
              (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)))) := by
  have hprime := tendsto_two_mul_nat_atTop.eventually
    (eventually_sum_psiNat_slowAmbientSmoothPrimeRange_le n)
  filter_upwards [hprime, eventually_ge_atTop (2 : ℕ)] with x hsum hx
  have hcutoff : 0 < taoTypicalLengthCutoff x := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlog 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  have hfinite := card_taoShortSmoothPrimeFailureUnion_cast_le
    (taoSlowAmbientSmoothPrimeRange n (2 * x)) hcutoff
  have hfinite' :
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowAmbientSmoothPrimeRange n (2 * x))).card : ℝ) ≤
        4 * (taoTypicalLengthCutoff x : ℝ) *
          ∑ p ∈ taoSlowAmbientSmoothPrimeRange n (2 * x),
            (psiNat ((2 * x) / p ^ 2) p : ℝ) := by
    simpa only [badIntervalCofactorBudget] using hfinite
  exact hfinite'.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- After absorbing the fixed number of cells and all dyadic lengths, the
ambient interval union retains half of the moving-grid exponent margin. -/
theorem eventually_card_taoSlowAmbientSmoothPrimeFailureUnion_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowAmbientSmoothPrimeRange n (2 * x))).card : ℝ) ≤
        (2 * x : ℕ) / (taoZ (2 * x)) ^
          (2 + 1 / (16 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  let C : ℝ := 4 * ((taoSlowGridStop n : ℝ) + 1)
  let δ : ℝ := 1 / (16 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  have habsorb := tendsto_two_mul_nat_atTop.eventually
    (eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow hC hδ)
  filter_upwards [eventually_card_taoSlowAmbientSmoothPrimeFailureUnion_raw n,
    habsorb, eventually_ge_atTop (1 : ℕ)] with x hunion habsorb' hx
  have hlength : C * (taoTypicalLengthCutoff x : ℝ) ≤
      (taoZ (2 * x)) ^ δ := by
    calc
      C * (taoTypicalLengthCutoff x : ℝ) ≤
          C * (taoTypicalLengthCutoff (2 * x) : ℝ) := by
        gcongr
        exact_mod_cast taoTypicalLengthCutoff_le_two_mul hx
      _ ≤ (taoZ (2 * x)) ^ δ := habsorb'
  have hzPos : 0 < taoZ (2 * x) := taoZ_pos _
  have hexponent :
      2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
        δ + (2 + 1 / (16 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
    dsimp only [δ]
    ring
  calc
    ((taoShortSmoothPrimeFailureUnion x
        (taoSlowAmbientSmoothPrimeRange n (2 * x))).card : ℝ) ≤
        4 * (taoTypicalLengthCutoff x : ℝ) *
          (((taoSlowGridStop n : ℝ) + 1) *
            ((2 * x : ℕ) / (taoZ (2 * x)) ^
              (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)))) := hunion
    _ = (C * (taoTypicalLengthCutoff x : ℝ)) *
          ((2 * x : ℕ) / (taoZ (2 * x)) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
      dsimp only [C]
      ring
    _ ≤ (taoZ (2 * x)) ^ δ *
          ((2 * x : ℕ) / (taoZ (2 * x)) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
      gcongr
    _ = (2 * x : ℕ) / (taoZ (2 * x)) ^
          (2 + 1 / (16 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
      rw [hexponent, Real.rpow_add hzPos]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hzPos δ)]

/-- Source-scale estimate for the entire moving smooth-prime band below the
row's anatomy cutoff. -/
theorem eventually_card_taoSlowSourceSmoothPrimeFailureUnion_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceSmoothPrimeRange n x)).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^
          (2 + 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  let δ : ℝ := 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  have hzPowerTop : Tendsto (fun z : ℝ => z ^ δ) atTop atTop :=
    tendsto_rpow_atTop hδ
  filter_upwards [eventually_taoSlowSourceSmoothPrimeRange_subset n,
    eventually_card_taoSlowAmbientSmoothPrimeFailureUnion_le n,
    eventually_taoZ_le_taoZ_two_mul,
    (hzPowerTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))] with x hsubset hunion hzMono hzPower
  have hcard : (taoShortSmoothPrimeFailureUnion x
      (taoSlowSourceSmoothPrimeRange n x)).card ≤
        (taoShortSmoothPrimeFailureUnion x
          (taoSlowAmbientSmoothPrimeRange n (2 * x))).card :=
    Finset.card_le_card (taoShortSmoothPrimeFailureUnion_mono hsubset)
  have hcardReal :
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceSmoothPrimeRange n x)).card : ℝ) ≤
        ((taoShortSmoothPrimeFailureUnion x
          (taoSlowAmbientSmoothPrimeRange n (2 * x))).card : ℝ) := by
    exact_mod_cast hcard
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hpowMono : (taoZ x) ^ (2 + 2 * δ) ≤
      (taoZ (2 * x)) ^ (2 + 2 * δ) :=
    Real.rpow_le_rpow hzPos.le hzMono (by positivity)
  have hscale :
      (2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 2 * δ) ≤
        (2 * (x : ℝ)) / (taoZ x) ^ (2 + 2 * δ) := by
    have hfirst := div_le_div_of_nonneg_left
      (show (0 : ℝ) ≤ (2 * x : ℕ) by positivity)
      (Real.rpow_pos_of_pos hzPos _) hpowMono
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfirst
  have hcoeff : (2 : ℝ) / (taoZ x) ^ δ ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hzPos _)).2 hzPower
  have hweakExponent :
      2 + 1 / (16 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
        2 + 2 * δ := by
    dsimp only [δ]
    ring
  have hfinalExponent :
      2 + 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
        2 + δ := by rfl
  calc
    ((taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceSmoothPrimeRange n x)).card : ℝ) ≤
        ((taoShortSmoothPrimeFailureUnion x
          (taoSlowAmbientSmoothPrimeRange n (2 * x))).card : ℝ) := hcardReal
    _ ≤ (2 * x : ℕ) / (taoZ (2 * x)) ^
        (2 + 1 / (16 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := hunion
    _ = (2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 2 * δ) := by
      rw [hweakExponent]
    _ ≤ (2 * (x : ℝ)) / (taoZ x) ^ (2 + 2 * δ) := hscale
    _ = ((2 : ℝ) / (taoZ x) ^ δ) *
        ((x : ℝ) / (taoZ x) ^ (2 + δ)) := by
      rw [show 2 + 2 * δ = δ + (2 + δ) by ring,
        Real.rpow_add hzPos]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hzPos δ),
        ne_of_gt (Real.rpow_pos_of_pos hzPos (2 + δ))]
    _ ≤ 1 * ((x : ℝ) / (taoZ x) ^ (2 + δ)) := by
      exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = (x : ℝ) / (taoZ x) ^
        (2 + 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
      rw [one_mul, hfinalExponent]

/-! ## The moving smooth-prime band above the upper anatomy cutoff -/

def taoSlowHighGridIndices (n : ℕ) : Finset ℕ :=
  Finset.Ico (taoSlowHighGridStart n) (taoSlowGridSize n)

noncomputable def taoSlowHighGridPrimeUnion (n X : ℕ) : Finset ℕ :=
  (taoSlowHighGridIndices n).biUnion fun k =>
    taoOneTermExponentPrimeBand
      (taoOneTermGridExponent (taoSlowGridSize n) k)
      (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X

/-- Ambient high-prime cover from exponent `1+1/d` through exponent three. -/
noncomputable def taoSlowAmbientHighPrimeRange (n X : ℕ) : Finset ℕ :=
  taoSlowHighGridPrimeUnion n X ∪
    taoOneTermExponentPrimeBand (2 : ℝ) (3 : ℝ) X

/-- Literal source high-prime range above `z^(1+2/d)` and below the source
square threshold. -/
noncomputable def taoSlowSourceHighPrimeRange (n x : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 (2 * x).sqrt).filter Nat.Prime).filter fun p =>
    taoOneTermExponentCutoff (taoSlowUpperExponent n) x < p ∧
      p ≤ taoTypicalSquareThreshold x

theorem eventually_sum_psiNat_slowHighGridBand_le
    {n k : ℕ} (hk : k ∈ taoSlowHighGridIndices n) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent (taoSlowGridSize n) k)
          (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (X : ℝ) / (taoZ X) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  have heps : (0 : ℝ) <
      1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) := by
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  filter_upwards [eventually_sum_psiNat_gridPrimeBand_le
      (K := taoSlowGridSize n) (k := k) (taoSlowGridSize_pos n) heps,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      X hband hz
  have hmargin := two_add_slowHighGridMargin_le
    (n := n) (k := k) (by simpa only [taoSlowHighGridIndices] using hk)
  have hdouble :
      1 / (4 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
        2 * (1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by ring
  rw [hdouble] at hmargin
  have hexponent :
      2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
        taoOneTermGridExponent (taoSlowGridSize n) k +
          1 / taoOneTermGridExponent (taoSlowGridSize n) (k + 1) -
            1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hz hexponent
  exact hband.trans (div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (taoZ_pos X) _) hpow)

theorem eventually_forall_sum_psiNat_slowHighGridBand_le (n : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ k ∈ taoSlowHighGridIndices n,
      (∑ p ∈ taoOneTermExponentPrimeBand
          (taoOneTermGridExponent (taoSlowGridSize n) k)
          (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (X : ℝ) / (taoZ X) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  rw [Filter.eventually_all_finset]
  intro k hk
  exact eventually_sum_psiNat_slowHighGridBand_le hk

theorem eventually_sum_psiNat_slowTwoToThreeBand_le (n : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ taoOneTermExponentPrimeBand (2 : ℝ) (3 : ℝ) X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (X : ℝ) / (taoZ X) ^
          (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  filter_upwards [eventually_sum_psiNat_largeSmoothTwoToThreeBand_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      X hband hz
  have hd : (10 : ℝ) ≤ taoSlowCutoffDenominator n := by
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hmargin : 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
      1 / 200 := by
    have hden : (0 : ℝ) < 8 * (taoSlowCutoffDenominator n : ℝ) ^ 2 := by
      positivity
    rw [div_le_div_iff_of_pos_left (by norm_num) hden (by norm_num)]
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hz (by linarith :
      2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤ 2 + 1 / 200)
  exact hband.trans (div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (taoZ_pos X) _) hpow)

theorem eventually_sum_psiNat_slowAmbientHighPrimeRange_le (n : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (∑ p ∈ taoSlowAmbientHighPrimeRange n X,
          (psiNat (X / p ^ 2) p : ℝ)) ≤
        (((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1) *
          ((X : ℝ) / (taoZ X) ^
            (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
  filter_upwards [eventually_forall_sum_psiNat_slowHighGridBand_le n,
    eventually_sum_psiNat_slowTwoToThreeBand_le n] with X hbands hlast
  let T : ℝ := (X : ℝ) / (taoZ X) ^
    (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))
  let f : ℕ → ℝ := fun p => (psiNat (X / p ^ 2) p : ℝ)
  have hgrid : (∑ p ∈ taoSlowHighGridPrimeUnion n X, f p) ≤
      ((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) * T := by
    calc
      (∑ p ∈ taoSlowHighGridPrimeUnion n X, f p) ≤
          ∑ k ∈ taoSlowHighGridIndices n,
            ∑ p ∈ taoOneTermExponentPrimeBand
              (taoOneTermGridExponent (taoSlowGridSize n) k)
              (taoOneTermGridExponent (taoSlowGridSize n) (k + 1)) X,
              f p := by
        exact sum_biUnion_le_sum_of_nonneg _ _ f (fun _ => by positivity)
      _ ≤ ∑ _k ∈ taoSlowHighGridIndices n, T := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [T, f] using hbands k hk
      _ = ((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) * T := by
        simp [taoSlowHighGridIndices]
  calc
    (∑ p ∈ taoSlowAmbientHighPrimeRange n X,
        (psiNat (X / p ^ 2) p : ℝ)) ≤
        (∑ p ∈ taoSlowHighGridPrimeUnion n X, f p) +
          ∑ p ∈ taoOneTermExponentPrimeBand (2 : ℝ) (3 : ℝ) X, f p := by
      exact sum_union_le_add_sum_of_nonneg _ _ f (fun _ => by positivity)
    _ ≤ ((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) * T + T :=
      add_le_add hgrid (by simpa only [T, f] using hlast)
    _ = (((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1) * T :=
      by ring

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem eventually_taoSlowSourceHighPrimeRange_subset (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowSourceHighPrimeRange n x ⊆
        taoSlowAmbientHighPrimeRange n (2 * x) := by
  filter_upwards [eventually_exponentCutoff_two_mul_le_of_lt
      (α := taoSlowAmbientLowerExponent n) (β := taoSlowUpperExponent n)
      (zero_lt_one.trans (one_lt_taoSlowAmbientLowerExponent n))
      (taoSlowAmbientLowerExponent_lt_upper n),
    eventually_exponentCutoff_le_two_mul_of_le
      (α := (3 : ℝ)) (β := (3 : ℝ)) (by norm_num) le_rfl] with
      x hlower hupper
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpUpper : p ≤ taoOneTermExponentCutoff (3 : ℝ) (2 * x) := by
    rw [taoOneTermExponentCutoff_three_eq_taoTypicalSquareThreshold] at hupper
    exact hpData.2.2.trans hupper
  have hpExpanded : p ∈ taoOneTermExponentPrimeBand
      (taoSlowAmbientLowerExponent n) (3 : ℝ) (2 * x) :=
    Finset.mem_filter.mpr
      ⟨hpData.1, lt_of_le_of_lt hlower hpData.2.1, hpUpper⟩
  rw [taoSlowAmbientHighPrimeRange]
  by_cases hpTwo : p ≤ taoOneTermExponentCutoff (2 : ℝ) (2 * x)
  · apply Finset.mem_union_left
    rw [taoSlowHighGridPrimeUnion]
    have hpGridBand : p ∈ taoOneTermExponentPrimeBand
        (taoOneTermGridExponent (taoSlowGridSize n) (taoSlowHighGridStart n))
        (taoOneTermGridExponent (taoSlowGridSize n) (taoSlowGridSize n))
        (2 * x) := by
      rw [taoOneTermGridExponent_slowHighGridStart n,
        taoOneTermGridExponent_self (taoSlowGridSize_pos n)]
      exact Finset.mem_filter.mpr
        ⟨hpData.1, (Finset.mem_filter.mp hpExpanded).2.1, hpTwo⟩
    exact exponentPrimeBand_gridEndpoints_subset_biUnion
      (taoSlowHighGridStart_lt_gridSize n) hpGridBand
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      ⟨hpData.1, Nat.lt_of_not_ge hpTwo,
        (Finset.mem_filter.mp hpExpanded).2.2⟩

/-- The source high-prime branch has the same moving positive margin as the
lower smooth branch. -/
theorem eventually_card_taoSlowSourceHighPrimeFailureUnion_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceHighPrimeRange n x)).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^
          (2 + 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  let C : ℝ := 4 *
    ((((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1))
  let δ : ℝ := 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  have hprime := tendsto_two_mul_nat_atTop.eventually
    (eventually_sum_psiNat_slowAmbientHighPrimeRange_le n)
  have habsorb := tendsto_two_mul_nat_atTop.eventually
    (eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow
      hC (show 0 < δ by exact hδ))
  have hzPowerTop : Tendsto (fun z : ℝ => z ^ δ) atTop atTop :=
    tendsto_rpow_atTop hδ
  filter_upwards [eventually_taoSlowSourceHighPrimeRange_subset n,
    hprime, habsorb, eventually_ge_atTop (2 : ℕ),
    eventually_taoZ_le_taoZ_two_mul,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (hzPowerTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))] with
      x hsubset hsum habsorb' hx hzMono hzOne hzPower
  have hcutoff : 0 < taoTypicalLengthCutoff x := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlog 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  have hfinite := card_taoShortSmoothPrimeFailureUnion_cast_le
    (taoSlowAmbientHighPrimeRange n (2 * x)) hcutoff
  have hambient :
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowAmbientHighPrimeRange n (2 * x))).card : ℝ) ≤
        (taoZ (2 * x)) ^ δ *
          ((2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 4 * δ)) := by
    have hfinite' := hfinite.trans
      (mul_le_mul_of_nonneg_left hsum (by positivity))
    have hlength : C * (taoTypicalLengthCutoff x : ℝ) ≤
        (taoZ (2 * x)) ^ δ := by
      calc
        C * (taoTypicalLengthCutoff x : ℝ) ≤
            C * (taoTypicalLengthCutoff (2 * x) : ℝ) := by
          gcongr
          exact_mod_cast taoTypicalLengthCutoff_le_two_mul (by omega : 1 ≤ x)
        _ ≤ (taoZ (2 * x)) ^ δ := habsorb'
    have hexponent :
        2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2) =
          2 + 4 * δ := by dsimp only [δ]; ring
    calc
      ((taoShortSmoothPrimeFailureUnion x
          (taoSlowAmbientHighPrimeRange n (2 * x))).card : ℝ) ≤
          4 * (taoTypicalLengthCutoff x : ℝ) *
            (((taoSlowGridSize n - taoSlowHighGridStart n : ℕ) : ℝ) + 1) *
              ((2 * x : ℕ) / (taoZ (2 * x)) ^
                (2 + 1 / (8 * (taoSlowCutoffDenominator n : ℝ) ^ 2))) := by
        simpa only [badIntervalCofactorBudget, mul_assoc] using hfinite'
      _ = (C * (taoTypicalLengthCutoff x : ℝ)) *
          ((2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 4 * δ)) := by
        rw [← hexponent]
        dsimp only [C]
        ring
      _ ≤ (taoZ (2 * x)) ^ δ *
          ((2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 4 * δ)) := by
        exact mul_le_mul_of_nonneg_right hlength
          (div_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (taoZ_pos (2 * x)).le _))
  have hzTwoPos : 0 < taoZ (2 * x) := taoZ_pos _
  have hambientWeak :
      ((taoShortSmoothPrimeFailureUnion x
        (taoSlowAmbientHighPrimeRange n (2 * x))).card : ℝ) ≤
        (2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 3 * δ) := by
    calc
      _ ≤ (taoZ (2 * x)) ^ δ *
          ((2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 4 * δ)) := hambient
      _ = (2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 3 * δ) := by
        rw [show 2 + 4 * δ = δ + (2 + 3 * δ) by ring,
          Real.rpow_add hzTwoPos]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hzTwoPos δ)]
  have hcard : (taoShortSmoothPrimeFailureUnion x
      (taoSlowSourceHighPrimeRange n x)).card ≤
        (taoShortSmoothPrimeFailureUnion x
          (taoSlowAmbientHighPrimeRange n (2 * x))).card :=
    Finset.card_le_card (taoShortSmoothPrimeFailureUnion_mono hsubset)
  have hpowMono : (taoZ x) ^ (2 + 3 * δ) ≤
      (taoZ (2 * x)) ^ (2 + 3 * δ) :=
    Real.rpow_le_rpow (taoZ_pos x).le hzMono (by positivity)
  have hscale : (2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 3 * δ) ≤
      (2 * (x : ℝ)) / (taoZ x) ^ (2 + 3 * δ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      div_le_div_of_nonneg_left
        (show (0 : ℝ) ≤ (2 * x : ℕ) by positivity)
        (Real.rpow_pos_of_pos (taoZ_pos x) _) hpowMono
  have hcoeff : (2 : ℝ) / (taoZ x) ^ δ ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos (taoZ_pos x) _)).2 hzPower
  calc
    ((taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceHighPrimeRange n x)).card : ℝ) ≤
        ((taoShortSmoothPrimeFailureUnion x
          (taoSlowAmbientHighPrimeRange n (2 * x))).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (2 * x : ℕ) / (taoZ (2 * x)) ^ (2 + 3 * δ) := hambientWeak
    _ ≤ (2 * (x : ℝ)) / (taoZ x) ^ (2 + 3 * δ) := hscale
    _ = ((2 : ℝ) / (taoZ x) ^ δ) *
        ((x : ℝ) / (taoZ x) ^ (2 + 2 * δ)) := by
      rw [show 2 + 3 * δ = δ + (2 + 2 * δ) by ring,
        Real.rpow_add (taoZ_pos x)]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos (taoZ_pos x) δ),
        ne_of_gt (Real.rpow_pos_of_pos (taoZ_pos x) (2 + 2 * δ))]
    _ ≤ (x : ℝ) / (taoZ x) ^ (2 + 2 * δ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcoeff
          (div_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (taoZ_pos x).le _))
    _ ≤ (x : ℝ) / (taoZ x) ^
        (2 + 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
      have hexponent :
          2 + 1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2) ≤
            2 + 2 * δ := by
        dsimp only [δ]
        have : (0 : ℝ) ≤
            1 / (32 * (taoSlowCutoffDenominator n : ℝ) ^ 2) := by positivity
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hzOne hexponent
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg x)
        (Real.rpow_pos_of_pos (taoZ_pos x) _) hpow

/-! ## The moving deficient-factor branch above the anatomy cutoff -/

/-- Uniform floor-removal estimate for every fixed positive exponent. -/
theorem eventually_one_div_taoZPowerFloor_sub_one_le_general
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      1 / ((taoZPowerFloor α x - 1 : ℕ) : ℝ) ≤
        2 / (taoZ x) ^ α := by
  have hpower : Tendsto (fun x => (taoZ x) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_taoZ_atTop
  filter_upwards [hpower.eventually (eventually_ge_atTop (4 : ℝ))] with x hx
  let Z : ℝ := (taoZ x) ^ α
  have hfloorLt : Z < (taoZPowerFloor α x : ℝ) + 1 := by
    simpa only [taoZPowerFloor, Z] using Nat.lt_floor_add_one Z
  have hfloorOne : 1 ≤ taoZPowerFloor α x := by
    have hthree : (3 : ℝ) < (taoZPowerFloor α x : ℝ) := by linarith
    have hthreeNat : 3 < taoZPowerFloor α x := by exact_mod_cast hthree
    omega
  have hden : Z / 2 ≤ ((taoZPowerFloor α x - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfloorOne]
    norm_num at hfloorLt ⊢
    change 4 ≤ Z at hx
    linarith
  have hZpos : 0 < Z := by dsimp only [Z]; positivity
  calc
    1 / ((taoZPowerFloor α x - 1 : ℕ) : ℝ) ≤ 1 / (Z / 2) :=
      one_div_le_one_div_of_le (half_pos hZpos) hden
    _ = 2 / (taoZ x) ^ α := by
      dsimp only [Z]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos (taoZ_pos x) _)]

/-- The complete fixed combinatorial and logarithmic loss in the deficient
branch is negligible compared with every fixed positive power of `z`. -/
theorem eventually_deficientPolylogFactor_le_taoZ_rpow_general
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      16000 * (taoTypicalLengthCutoff x : ℝ) *
          (1 + Real.log (taoTypicalSquareThreshold x : ℝ)) ^ (999 : ℕ) ≤
        (taoZ x) ^ δ := by
  let C : ℝ := 32000 * (3 : ℝ) ^ (999 : ℕ)
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hconst : Tendsto (fun x : ℕ =>
      Real.log C / Real.log (taoZ x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogZ
  have hiter : Tendsto (fun x : ℕ =>
      1019 * (iteratedLog x / Real.log (taoZ x))) atTop (𝓝 0) := by
    simpa using tendsto_iteratedLog_div_log_taoZ_zero.const_mul 1019
  filter_upwards [eventually_taoTypicalSquareThreshold_le_two_mul,
    hconst.eventually (Iio_mem_nhds (half_pos hδ)),
    hiter.eventually (Iio_mem_nhds (half_pos hδ)),
    hlogZ.eventually (eventually_gt_atTop (0 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with
      x hthreshold hconstBound hiterBound hlogZPos hlogX hx
  change 1 ≤ Real.log (x : ℝ) at hlogX
  have hlogXPos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlogX
  have hlengthLt : (taoTypicalLengthCutoff x : ℝ) <
      (Real.log (x : ℝ)) ^ (20 : ℕ) + 1 := by
    simpa only [taoTypicalLengthCutoff] using
      Nat.ceil_lt_add_one (pow_nonneg hlogXPos.le 20)
  have hPone : 1 ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := one_le_pow₀ hlogX
  have hlength : (taoTypicalLengthCutoff x : ℝ) ≤
      2 * (Real.log (x : ℝ)) ^ (20 : ℕ) := by linarith
  have hthresholdPos : (0 : ℝ) < taoTypicalSquareThreshold x := by
    exact_mod_cast taoTypicalSquareThreshold_pos x
  have htwoXPos : (0 : ℝ) < (2 * x : ℕ) := by positivity
  have hlogThreshold : Real.log (taoTypicalSquareThreshold x : ℝ) ≤
      Real.log (2 * x : ℕ) :=
    Real.strictMonoOn_log.monotoneOn hthresholdPos htwoXPos
      (by exact_mod_cast hthreshold)
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (x : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show (0 : ℝ) < x by exact_mod_cast (show 0 < x by omega))
      (by exact_mod_cast hx)
  have hlogTwoX : Real.log (2 * x : ℕ) =
      Real.log 2 + Real.log (x : ℝ) := by
    rw [show ((2 * x : ℕ) : ℝ) = 2 * (x : ℝ) by norm_num,
      Real.log_mul (by norm_num) (by positivity)]
  have hB : 1 + Real.log (taoTypicalSquareThreshold x : ℝ) ≤
      3 * Real.log (x : ℝ) := by
    rw [hlogTwoX] at hlogThreshold
    linarith
  have hB0 : 0 ≤ 1 + Real.log (taoTypicalSquareThreshold x : ℝ) := by
    have : 0 ≤ Real.log (taoTypicalSquareThreshold x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast
        (taoTypicalSquareThreshold_pos x : 0 < taoTypicalSquareThreshold x))
    linarith
  have hpoly :
      16000 * (taoTypicalLengthCutoff x : ℝ) *
          (1 + Real.log (taoTypicalSquareThreshold x : ℝ)) ^ (999 : ℕ) ≤
        C * (Real.log (x : ℝ)) ^ (1019 : ℕ) := by
    calc
      16000 * (taoTypicalLengthCutoff x : ℝ) *
          (1 + Real.log (taoTypicalSquareThreshold x : ℝ)) ^ (999 : ℕ) ≤
          16000 * (2 * (Real.log (x : ℝ)) ^ (20 : ℕ)) *
            (3 * Real.log (x : ℝ)) ^ (999 : ℕ) := by gcongr
      _ = C * (Real.log (x : ℝ)) ^ (1019 : ℕ) := by
        dsimp only [C]
        rw [mul_pow]
        rw [show (32000 : ℝ) = 16000 * 2 by norm_num,
          show (1019 : ℕ) = 20 + 999 by norm_num, pow_add]
        ac_rfl
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hconstMul : Real.log C <
      (δ / 2) * Real.log (taoZ x) :=
    (div_lt_iff₀ hlogZPos).mp hconstBound
  have hiterDiv :
      (1019 * iteratedLog x) / Real.log (taoZ x) < δ / 2 := by
    calc
      (1019 * iteratedLog x) / Real.log (taoZ x) =
          1019 * (iteratedLog x / Real.log (taoZ x)) := by ring
      _ < δ / 2 := hiterBound
  have hiterMul : 1019 * iteratedLog x <
      (δ / 2) * Real.log (taoZ x) :=
    (div_lt_iff₀ hlogZPos).mp hiterDiv
  have hlogBound :
      Real.log (C * (Real.log (x : ℝ)) ^ (1019 : ℕ)) ≤
        δ * Real.log (taoZ x) := by
    rw [Real.log_mul hCpos.ne' (pow_pos hlogXPos (1019 : ℕ)).ne',
      Real.log_pow]
    change Real.log C + 1019 * iteratedLog x ≤ δ * Real.log (taoZ x)
    linarith
  exact hpoly.trans (Real.le_rpow_of_log_le (taoZ_pos x) hlogBound)

/-- Distinguished-prime range used by the moving deficient-factor count,
from the anatomy floor through the moving upper cutoff. -/
noncomputable def taoSlowDeficientPrimeRange (n x : ℕ) : Finset ℕ :=
  deficientPrimeFactorRange (taoZPowerFloor (taoSlowLowerExponent n) x)
    (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)

/-- Uniform smooth-cofactor estimate on the full moving deficient range. -/
theorem eventually_taoSlowDeficientSmoothPointwiseBound (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      DeficientSmoothPointwiseBound x
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoSlowDeficientPrimeRange n x)
        (1 / (taoZ x) ^
          (1 / taoSlowLowerExponent n -
            1 / (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  have hε : (0 : ℝ) < 1 / (taoSlowCutoffDenominator n : ℝ) ^ 2 := by
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    positivity
  filter_upwards [eventually_deficientSmoothPointwiseBound_uniform
      (α := taoSlowLowerExponent n) (β := taoSlowUpperExponent n)
      (ε := 1 / (taoSlowCutoffDenominator n : ℝ) ^ 2)
      (taoSlowLowerExponent_pos n)
      (by linarith [one_lt_taoSlowAmbientLowerExponent n,
        taoSlowAmbientLowerExponent_lt_upper n]) hε] with x huniform
  intro p₀ hp₀ qs hqs
  have hpData := mem_deficientPrimeFactorRange.mp hp₀
  exact huniform p₀ hpData.1.one_le hpData.2.2 qs hqs

set_option maxRecDepth 10000 in
/-- Exact pre-absorption estimate for the full moving deficient union. -/
theorem eventually_card_taoSlowDeficientPrimeFailureUnion_raw (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoDeficientPrimeFailureUnion x (taoTypicalSquareThreshold x)
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
        (taoSlowDeficientPrimeRange n x)).card : ℝ) ≤
      4 * (taoTypicalLengthCutoff x : ℝ) *
        (((1 / (taoZ x) ^
            (1 / taoSlowLowerExponent n -
              1 / (taoSlowCutoffDenominator n : ℝ) ^ 2)) * (2 * x : ℕ)) *
          ((1 / ((taoZPowerFloor (taoSlowLowerExponent n) x - 1 : ℕ) : ℝ)) *
            (1000 * (1 + Real.log
              (taoOneTermExponentCutoff (taoSlowUpperExponent n) x : ℝ)) ^
              (999 : ℕ)))) := by
  filter_upwards [eventually_taoSlowDeficientSmoothPointwiseBound n,
    (tendsto_taoZPowerFloor_atTop (taoSlowLowerExponent_pos n)).eventually
      (eventually_ge_atTop (2 : ℕ)),
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with x hpsi hlower hupper hx
  have hexponents : taoSlowLowerExponent n ≤ taoSlowUpperExponent n := by
    rw [taoSlowLowerExponent, taoSlowUpperExponent]
    have hd : (0 : ℝ) < taoSlowCutoffDenominator n := by
      exact_mod_cast taoSlowCutoffDenominator_pos n
    have hdiv : 0 ≤ 2 / (taoSlowCutoffDenominator n : ℝ) :=
      div_nonneg (by norm_num) hd.le
    linarith
  have hfloorLower :
      taoZPowerFloor (taoSlowLowerExponent n) x ≤
        taoOneTermExponentCutoff (taoSlowLowerExponent n) x := by
    have hfloor :
        (taoZPowerFloor (taoSlowLowerExponent n) x : ℝ) ≤
          (taoZ x) ^ taoSlowLowerExponent n :=
      Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
    have hceil :
        (taoZ x) ^ taoSlowLowerExponent n ≤
          (taoOneTermExponentCutoff (taoSlowLowerExponent n) x : ℝ) :=
      Nat.le_ceil _
    exact_mod_cast hfloor.trans hceil
  have hupperCutoff :
      2 ≤ taoOneTermExponentCutoff (taoSlowUpperExponent n) x :=
    hlower.trans <| hfloorLower.trans <|
        taoOneTermExponentCutoff_mono_of_one_le hupper hexponents
  have hcutoff : 0 < taoTypicalLengthCutoff x := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlog 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  exact card_taoDeficientPrimeFailureUnion_cast_le_of_pointwise
    (x := x) (squareThreshold := taoTypicalSquareThreshold x)
    (lowerPrime := taoZPowerFloor (taoSlowLowerExponent n) x)
    (upperPrime := taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
    (P := taoSlowDeficientPrimeRange n x)
    (saving := 1 / (taoZ x) ^
      (1 / taoSlowLowerExponent n -
        1 / (taoSlowCutoffDenominator n : ℝ) ^ 2))
    (one_div_nonneg.mpr (Real.rpow_nonneg (taoZ_pos x).le _))
    hcutoff hlower hupperCutoff (fun _ hp => hp) hpsi

/-- For every fixed row, the entire deficient-factor branch has a positive
quantitative margin beyond `z^2`. -/
theorem eventually_card_taoSlowDeficientPrimeFailureUnion_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoDeficientPrimeFailureUnion x (taoTypicalSquareThreshold x)
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
        (taoSlowDeficientPrimeRange n x)).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^
          (2 + 1 / (taoSlowCutoffDenominator n : ℝ) ^ 2) := by
  let d : ℝ := taoSlowCutoffDenominator n
  let α : ℝ := taoSlowLowerExponent n
  let δ : ℝ := 1 / d ^ 2
  have hd : (10 : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hdPos : 0 < d := by linarith
  have hαDef : α = 1 - 2 / d := by
    simp only [α, d, taoSlowLowerExponent]
  have hαPos : 0 < α := by
    simpa only [α] using taoSlowLowerExponent_pos n
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hexcess : 2 + 3 * δ ≤ α + 1 / α := by
    have hαLe : α ≤ 1 := by
      rw [hαDef]
      exact sub_le_self 1 (div_nonneg (by norm_num) hdPos.le)
    have hidentity : α + 1 / α - 2 = (1 - α) ^ 2 / α := by
      field_simp [hαPos.ne']
      ring
    have hfour : 4 * δ ≤ (1 - α) ^ 2 := by
      rw [hαDef]
      dsimp only [δ]
      field_simp
      norm_num
    have hdivide : (1 - α) ^ 2 ≤ (1 - α) ^ 2 / α := by
      rw [le_div_iff₀ hαPos]
      nlinarith [sq_nonneg (1 - α)]
    calc
      2 + 3 * δ ≤ 2 + (1 - α) ^ 2 / α := by
        linarith
      _ = α + 1 / α := by linarith
  filter_upwards [eventually_card_taoSlowDeficientPrimeFailureUnion_raw n,
    eventually_one_div_taoZPowerFloor_sub_one_le_general
      (taoSlowLowerExponent_pos n),
    eventually_deficientPolylogFactor_le_taoZ_rpow_general hδ,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hraw hden hpoly hz
  let B : ℝ := 1 + Real.log (taoTypicalSquareThreshold x : ℝ)
  have hzPos : 0 < taoZ x := taoZ_pos x
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hthresholdOne : 1 ≤ taoTypicalSquareThreshold x :=
      taoTypicalSquareThreshold_pos x
    exact add_nonneg (by norm_num)
      (Real.log_nonneg (by exact_mod_cast hthresholdOne))
  have hupperCut :
      taoOneTermExponentCutoff (taoSlowUpperExponent n) x ≤
        taoTypicalSquareThreshold x := by
    rw [← taoOneTermExponentCutoff_three_eq_taoTypicalSquareThreshold]
    exact taoOneTermExponentCutoff_mono_of_one_le hz
      (le_of_lt (taoSlowUpperExponent_lt_three n))
  have hupperLog :
      1 + Real.log
          (taoOneTermExponentCutoff (taoSlowUpperExponent n) x : ℝ) ≤ B := by
    dsimp only [B]
    have hcast :
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x : ℝ) ≤
          (taoTypicalSquareThreshold x : ℝ) := by
      exact_mod_cast hupperCut
    have hcutPosNat :
        0 < taoOneTermExponentCutoff (taoSlowUpperExponent n) x := by
      unfold taoOneTermExponentCutoff
      exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (taoZ_pos x) _)
    have hcutPosReal :
        (0 : ℝ) < taoOneTermExponentCutoff (taoSlowUpperExponent n) x := by
      exact_mod_cast hcutPosNat
    simpa [add_comm] using
      add_le_add_left (Real.log_le_log hcutPosReal hcast) 1
  have hpoly' :
      16000 * (taoTypicalLengthCutoff x : ℝ) * B ^ (999 : ℕ) ≤
        (taoZ x) ^ δ := by
    simpa only [B, δ, d] using hpoly
  have hcombine (L X T Z₁ Z₂ : ℝ) (hZ₁ : Z₁ ≠ 0) (hZ₂ : Z₂ ≠ 0) :
      4 * L * ((1 / Z₁ * (2 * X)) * ((2 / Z₂) * (1000 * T))) =
        (16000 * L * T) * (X / (Z₁ * Z₂)) := by
    field_simp [hZ₁, hZ₂]
    ring
  have hcancel (X A D : ℝ) (hA : A ≠ 0) (hD : D ≠ 0) :
      A * (X / (A * D)) = X / D := by field_simp [hA, hD]
  calc
    ((taoDeficientPrimeFailureUnion x (taoTypicalSquareThreshold x)
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
        (taoSlowDeficientPrimeRange n x)).card : ℝ) ≤
      4 * (taoTypicalLengthCutoff x : ℝ) *
        (((1 / (taoZ x) ^ (1 / α - δ)) * (2 * x : ℕ)) *
          ((1 / ((taoZPowerFloor (taoSlowLowerExponent n) x - 1 : ℕ) : ℝ)) *
            (1000 * (1 + Real.log
              (taoOneTermExponentCutoff (taoSlowUpperExponent n) x : ℝ)) ^
                (999 : ℕ)))) := by
      simpa only [α, δ, d] using hraw
    _ ≤ 4 * (taoTypicalLengthCutoff x : ℝ) *
        (((1 / (taoZ x) ^ (1 / α - δ)) * (2 * x : ℕ)) *
          ((1 / ((taoZPowerFloor (taoSlowLowerExponent n) x - 1 : ℕ) : ℝ)) *
            (1000 * B ^ (999 : ℕ)))) := by
      gcongr
    _ ≤ 4 * (taoTypicalLengthCutoff x : ℝ) *
        (((1 / (taoZ x) ^ (1 / α - δ)) * (2 * x : ℕ)) *
          ((2 / (taoZ x) ^ α) * (1000 * B ^ (999 : ℕ)))) := by
      gcongr
    _ = (16000 * (taoTypicalLengthCutoff x : ℝ) * B ^ (999 : ℕ)) *
        ((x : ℝ) / (taoZ x) ^ ((1 / α - δ) + α)) := by
      rw [Real.rpow_add hzPos]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcombine
        (taoTypicalLengthCutoff x : ℝ) (x : ℝ) (B ^ (999 : ℕ))
        ((taoZ x) ^ (1 / α - δ)) ((taoZ x) ^ α)
        (ne_of_gt (Real.rpow_pos_of_pos hzPos _))
        (ne_of_gt (Real.rpow_pos_of_pos hzPos _))
    _ ≤ (taoZ x) ^ δ *
        ((x : ℝ) / (taoZ x) ^ ((1 / α - δ) + α)) := by
      exact mul_le_mul_of_nonneg_right hpoly'
        (div_nonneg (Nat.cast_nonneg x) (Real.rpow_nonneg hzPos.le _))
    _ = (x : ℝ) / (taoZ x) ^ ((1 / α - δ) + α - δ) := by
      rw [show (1 / α - δ) + α = δ + ((1 / α - δ) + α - δ) by ring,
        Real.rpow_add hzPos]
      convert hcancel (x : ℝ) ((taoZ x) ^ δ)
        ((taoZ x) ^ ((1 / α - δ) + α - δ))
        (ne_of_gt (Real.rpow_pos_of_pos hzPos _))
        (ne_of_gt (Real.rpow_pos_of_pos hzPos _)) using 1
      all_goals ring_nf
    _ ≤ (x : ℝ) / (taoZ x) ^ (2 + δ) := by
      have hexponent : 2 + δ ≤ (1 / α - δ) + α - δ := by
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hz hexponent
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg x)
        (Real.rpow_pos_of_pos hzPos _) hpow
    _ = (x : ℝ) / (taoZ x) ^
        (2 + 1 / (taoSlowCutoffDenominator n : ℝ) ^ 2) := by rfl

/-! ## Fixed-row Proposition 6.5 assembly -/

/-- Non-typical normalized intervals for row `n` of the moving cutoff
family. -/
noncomputable def taoSlowNonTypicalFailureIndices (n x : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    ∃ p₀ k m : ℕ,
      IsNonTypicalScaleNormalizedBadInterval x (taoTypicalLengthCutoff x)
        (taoTypicalSquareThreshold x)
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
        NH.1 NH.2 p₀ k m

/-- Actual interval union associated with one fixed moving-cutoff row. -/
noncomputable def taoSlowNonTypicalFailureUnion (n x : ℕ) : Finset ℕ := by
  classical
  exact (taoSlowNonTypicalFailureIndices n x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem mem_taoSlowNonTypicalFailureIndices {n x N H : ℕ} :
    (N, H) ∈ taoSlowNonTypicalFailureIndices n x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        ∃ p₀ k m : ℕ,
          IsNonTypicalScaleNormalizedBadInterval x (taoTypicalLengthCutoff x)
            (taoTypicalSquareThreshold x)
            (taoZPowerFloor (taoSlowLowerExponent n) x)
            (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
            N H p₀ k m := by
  classical
  simp [taoSlowNonTypicalFailureIndices]

/-- Eight exhaustive quantitative branches for one moving-cutoff row. -/
noncomputable def taoSlowProposition65FailureCover (n x : ℕ) : Finset ℕ :=
  taoLargeLengthFailureUnion x ∪
    (taoShortLargePrimeFailureUnion x ∪
      (taoLongModerateFailureUnion x ∪
        (taoLargeSquareFailureUnion x ∪
          (taoSmallPrimeFailureUnion x
              (taoOneTermExponentCutoff (2 / 5 : ℝ) x) ∪
            (taoShortSmoothPrimeFailureUnion x
                (taoSlowSourceSmoothPrimeRange n x) ∪
              (taoDeficientPrimeFailureUnion x
                  (taoTypicalSquareThreshold x)
                  (taoZPowerFloor (taoSlowLowerExponent n) x)
                  (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
                  (taoSlowDeficientPrimeRange n x) ∪
                taoShortSmoothPrimeFailureUnion x
                  (taoSlowSourceHighPrimeRange n x)))))))

/-- Flooring and ceiling the same positive real cutoff gives the required
ordered natural endpoints. -/
theorem taoZPowerFloor_le_taoOneTermExponentCutoff (α : ℝ) (x : ℕ) :
    taoZPowerFloor α x ≤ taoOneTermExponentCutoff α x := by
  have hfloor : (taoZPowerFloor α x : ℝ) ≤ (taoZ x) ^ α :=
    Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
  have hceil : (taoZ x) ^ α ≤
      (taoOneTermExponentCutoff α x : ℝ) := Nat.le_ceil _
  exact_mod_cast hfloor.trans hceil

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1200000 in
/-- Every non-typical interval in a fixed row belongs to one of its eight
quantitatively controlled failure unions. -/
theorem eventually_taoSlowNonTypicalFailureUnion_subset_cover (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      taoSlowNonTypicalFailureUnion n x ⊆
        taoSlowProposition65FailureCover n x := by
  classical
  have hαFiveFour : taoSlowLowerExponent n ≤ (5 / 4 : ℝ) := by
    have hlt := taoSlowAmbientUpperExponent_lt_one n
    have hαlt := (taoSlowLowerExponent_lt_ambient n).trans hlt
    linarith
  filter_upwards [eventually_exponentCutoff_sq_le
      (β := (5 / 4 : ℝ)) (by norm_num), eventually_ge_atTop (2 : ℕ),
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hcutSq hx hzOne
  intro a ha
  rw [taoSlowNonTypicalFailureUnion, Finset.mem_biUnion] at ha
  obtain ⟨⟨N, H⟩, hNH, haInterval⟩ := ha
  rw [mem_taoSlowNonTypicalFailureIndices] at hNH
  obtain ⟨hscale, p₀, k, m, hnon⟩ := hNH
  have hnorm := hnon.1
  have hpPrime := hnorm.2.2.1
  have hpTwo : 2 ≤ p₀ := hpPrime.two_le
  have hlargeLengthOrShort :
      (x : ℝ) ^ (7 / 50 : ℝ) ≤ (H : ℝ) ∨
        H < badIntervalLargePrimeLengthCutoff x := by
    by_cases hlarge : (x : ℝ) ^ (7 / 50 : ℝ) ≤ (H : ℝ)
    · exact Or.inl hlarge
    · right
      have hreal : (H : ℝ) < (x : ℝ) ^ (7 / 50 : ℝ) := lt_of_not_ge hlarge
      have hceil : (x : ℝ) ^ (7 / 50 : ℝ) ≤
          (badIntervalLargePrimeLengthCutoff x : ℝ) := Nat.le_ceil _
      exact_mod_cast hreal.trans_le hceil
  rcases hlargeLengthOrShort with hlarge | hprelimShort
  · rw [taoSlowProposition65FailureCover, Finset.mem_union]
    left
    rw [taoLargeLengthFailureUnion, Finset.mem_biUnion]
    exact ⟨(N, H), mem_taoLargeLengthFailureIndices.mpr ⟨hscale, hlarge⟩,
      haInterval⟩
  · by_cases hpLarge : x ^ 3 < p₀ ^ 20
    · rw [taoSlowProposition65FailureCover, Finset.mem_union]
      right; rw [Finset.mem_union]; left
      rw [taoShortLargePrimeFailureUnion, Finset.mem_biUnion]
      exact ⟨(N, H), mem_taoShortLargePrimeFailureIndices.mpr
        ⟨hscale, hprelimShort, p₀, k, m, hnorm, hpLarge⟩, haInterval⟩
    · have hpModerate : p₀ ^ 20 ≤ x ^ 3 := Nat.le_of_not_gt hpLarge
      by_cases hlong : taoTypicalLengthCutoff x ≤ H
      · rw [taoSlowProposition65FailureCover, Finset.mem_union]
        right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; left
        rw [taoLongModerateFailureUnion, Finset.mem_biUnion]
        exact ⟨(N, H), mem_taoLongModerateFailureIndices.mpr
          ⟨hscale, hlong, p₀, k, m, hnorm, hpModerate⟩, haInterval⟩
      · have hshort : H < taoTypicalLengthCutoff x := Nat.lt_of_not_ge hlong
        by_cases havoid : AvoidsSquareMultiplesAtLeast N H
            (taoTypicalSquareThreshold x)
        · have hpUpperSquare : p₀ ≤ taoTypicalSquareThreshold x :=
            (hnon.p₀_lt_squareThreshold_of_avoids havoid).le
          by_cases hpSmall :
              p₀ ≤ taoOneTermExponentCutoff (2 / 5 : ℝ) x
          · rw [taoSlowProposition65FailureCover, Finset.mem_union]
            right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
            rw [Finset.mem_union]; right; rw [Finset.mem_union]; left
            rw [taoSmallPrimeFailureUnion, Finset.mem_biUnion]
            exact ⟨(N, H), mem_taoSmallPrimeFailureIndices.mpr
              ⟨hscale, p₀, k, m, hnorm, hpSmall⟩, haInterval⟩
          · have hpAboveSmall :
                taoOneTermExponentCutoff (2 / 5 : ℝ) x < p₀ :=
              Nat.lt_of_not_ge hpSmall
            by_cases hpBelowAnatomy :
                p₀ ≤ taoOneTermExponentCutoff (taoSlowLowerExponent n) x
            · have hpCut : p₀ ≤ taoOneTermExponentCutoff (5 / 4 : ℝ) x :=
                hpBelowAnatomy.trans
                  (taoOneTermExponentCutoff_mono_of_one_le hzOne hαFiveFour)
              have hpSq : p₀ * p₀ ≤ x :=
                (Nat.mul_le_mul hpCut hpCut).trans
                  (by simpa [pow_two] using hcutSq)
              have hpBand : p₀ ∈ taoSlowSourceSmoothPrimeRange n x := by
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_filter.mpr
                    ⟨Finset.mem_Icc.mpr ⟨hpTwo, Nat.le_sqrt.mpr hpSq⟩,
                      hpPrime⟩,
                    hpAboveSmall, hpBelowAnatomy⟩
              rw [taoSlowProposition65FailureCover, Finset.mem_union]
              right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
              rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
              rw [Finset.mem_union]; left
              rw [taoShortSmoothPrimeFailureUnion, Finset.mem_biUnion]
              exact ⟨(N, H), mem_taoShortSmoothPrimeFailureIndices.mpr
                ⟨hscale, hshort, p₀, k, m, hnorm, hpBand⟩, haInterval⟩
            · have hpAboveAnatomy :
                  taoOneTermExponentCutoff (taoSlowLowerExponent n) x < p₀ :=
                Nat.lt_of_not_ge hpBelowAnatomy
              by_cases hpAtMostUpper :
                  p₀ ≤ taoOneTermExponentCutoff (taoSlowUpperExponent n) x
              · have hpBand : p₀ ∈ taoSlowDeficientPrimeRange n x := by
                  rw [taoSlowDeficientPrimeRange,
                    mem_deficientPrimeFactorRange]
                  exact ⟨hpPrime,
                    (taoZPowerFloor_le_taoOneTermExponentCutoff
                      (taoSlowLowerExponent n) x).trans hpAboveAnatomy.le,
                    hpAtMostUpper⟩
                rw [taoSlowProposition65FailureCover, Finset.mem_union]
                right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [Finset.mem_union]; right; rw [Finset.mem_union]; left
                rw [taoDeficientPrimeFailureUnion, Finset.mem_biUnion]
                refine ⟨(N, H), ?_, haInterval⟩
                rw [taoDeficientPrimeFailureIndices, Finset.mem_filter]
                exact ⟨hscale, hshort, havoid, p₀, k, m, hnon,
                  hpAtMostUpper, hpBand⟩
              · have hpHigh : p₀ ∈ taoSlowSourceHighPrimeRange n x := by
                  rw [taoSlowSourceHighPrimeRange, Finset.mem_filter]
                  exact ⟨Finset.mem_filter.mpr
                    ⟨Finset.mem_Icc.mpr
                      ⟨hpTwo, hnon.p₀_le_two_mul_sqrt⟩, hpPrime⟩,
                    Nat.lt_of_not_ge hpAtMostUpper, hpUpperSquare⟩
                rw [taoSlowProposition65FailureCover, Finset.mem_union]
                right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
                rw [taoShortSmoothPrimeFailureUnion, Finset.mem_biUnion]
                exact ⟨(N, H), mem_taoShortSmoothPrimeFailureIndices.mpr
                  ⟨hscale, hshort, p₀, k, m, hnorm, hpHigh⟩, haInterval⟩
        · rw [taoSlowProposition65FailureCover, Finset.mem_union]
          right; rw [Finset.mem_union]; right; rw [Finset.mem_union]; right
          rw [Finset.mem_union]; left
          rw [taoLargeSquareFailureUnion, Finset.mem_biUnion]
          exact ⟨(N, H), mem_taoLargeSquareFailureIndices.mpr
            ⟨hscale, hshort, havoid⟩, haInterval⟩

theorem card_union_seven_le {γ : Type*} [DecidableEq γ]
    (A B C D E F G : Finset γ) :
    (A ∪ (B ∪ (C ∪ (D ∪ (E ∪ (F ∪ G)))))).card ≤
      A.card + B.card + C.card + D.card + E.card + F.card + G.card := by
  have hA := Finset.card_union_le A (B ∪ (C ∪ (D ∪ (E ∪ (F ∪ G)))))
  have hB := Finset.card_union_le B (C ∪ (D ∪ (E ∪ (F ∪ G))))
  have hC := Finset.card_union_le C (D ∪ (E ∪ (F ∪ G)))
  have hD := Finset.card_union_le D (E ∪ (F ∪ G))
  have hE := Finset.card_union_le E (F ∪ G)
  have hF := Finset.card_union_le F G
  omega

theorem card_taoSlowProposition65FailureCover_le (n x : ℕ) :
    (taoSlowProposition65FailureCover n x).card ≤
      (taoLargeLengthFailureUnion x).card +
      (taoShortLargePrimeFailureUnion x).card +
      (taoLongModerateFailureUnion x).card +
      (taoLargeSquareFailureUnion x).card +
      (taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceSmoothPrimeRange n x)).card +
      (taoDeficientPrimeFailureUnion x
        (taoTypicalSquareThreshold x)
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
        (taoSlowDeficientPrimeRange n x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceHighPrimeRange n x)).card := by
  simpa only [taoSlowProposition65FailureCover] using card_union_eight_le
    (taoLargeLengthFailureUnion x)
    (taoShortLargePrimeFailureUnion x)
    (taoLongModerateFailureUnion x)
    (taoLargeSquareFailureUnion x)
    (taoSmallPrimeFailureUnion x
      (taoOneTermExponentCutoff (2 / 5 : ℝ) x))
    (taoShortSmoothPrimeFailureUnion x
      (taoSlowSourceSmoothPrimeRange n x))
    (taoDeficientPrimeFailureUnion x
      (taoTypicalSquareThreshold x)
      (taoZPowerFloor (taoSlowLowerExponent n) x)
      (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
      (taoSlowDeficientPrimeRange n x))
    (taoShortSmoothPrimeFailureUnion x
      (taoSlowSourceHighPrimeRange n x))

/-- Quantitative Proposition 6.5 for every fixed row of cutoffs approaching
exponent one.  The margin may depend on the row, which is exactly what the
subsequent countable diagonal requires. -/
theorem eventually_card_taoSlowNonTypicalFailureUnion_le (n : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
        (x : ℝ) / (taoZ x) ^
          (2 + 1 / (128 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := by
  obtain ⟨c, hc, hlargeLength⟩ :=
    exists_eventually_card_taoLargeLengthFailureUnion_cast_le
  let d : ℝ := taoSlowCutoffDenominator n
  let commonExponent : ℝ := 2 + 1 / (64 * d ^ 2)
  let finalExponent : ℝ := 2 + 1 / (128 * d ^ 2)
  let T : ℕ → ℝ := fun x => (x : ℝ) / (taoZ x) ^ commonExponent
  have hd : (10 : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast ten_le_taoSlowCutoffDenominator n
  have hdPos : 0 < d := by linarith
  have hcommonPos : 0 < commonExponent := by
    dsimp only [commonExponent]
    positivity
  have hcommonLtFinal : finalExponent < commonExponent := by
    dsimp only [commonExponent, finalExponent]
    have hdSqPos : 0 < d ^ 2 := sq_pos_of_pos hdPos
    have : 1 / (128 * d ^ 2) < 1 / (64 * d ^ 2) := by
      exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    linarith
  have hcommonLtThree : commonExponent < 3 := by
    dsimp only [commonExponent]
    have hdSq : (100 : ℝ) ≤ d ^ 2 := by nlinarith
    have hden : 0 < 64 * d ^ 2 := by positivity
    have hrecip : 1 / (64 * d ^ 2) < 1 :=
      (div_lt_one hden).2 (by nlinarith)
    linarith
  have hcommonLtFiveHalves : commonExponent < 5 / 2 := by
    dsimp only [commonExponent]
    have hdSq : (100 : ℝ) ≤ d ^ 2 := by nlinarith
    have hden : 0 < 64 * d ^ 2 := by positivity
    have hrecip : 1 / (64 * d ^ 2) < 1 / 2 :=
      (div_lt_iff₀ hden).2 (by nlinarith)
    linarith
  have hcommonLtTwelveFifths : commonExponent < 12 / 5 := by
    dsimp only [commonExponent]
    have hdSq : (100 : ℝ) ≤ d ^ 2 := by nlinarith
    have hden : 0 < 64 * d ^ 2 := by positivity
    have hrecip : 1 / (64 * d ^ 2) < 2 / 5 :=
      (div_lt_iff₀ hden).2 (by nlinarith)
    linarith
  have hcommonLtSmooth : commonExponent < 2 + 1 / (32 * d ^ 2) := by
    dsimp only [commonExponent]
    have : 1 / (64 * d ^ 2) < 1 / (32 * d ^ 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    linarith
  have hcommonLtDeficient : commonExponent < 2 + 1 / d ^ 2 := by
    dsimp only [commonExponent]
    have : 1 / (64 * d ^ 2) < 1 / d ^ 2 :=
      one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    linarith
  have hlargeLengthConvert :=
    eventually_nat_rpow_one_sub_le_self_div_taoZ_rpow
      hcommonPos hc
  have hlargePrimeConvert :=
    eventually_nat_rpow_one_sub_le_self_div_taoZ_rpow
      (A := commonExponent) (c := (1 / 200 : ℝ)) hcommonPos (by norm_num)
  have hlongConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := (3 : ℝ)) (b := commonExponent)
    (by norm_num) hcommonLtThree
  have hsquareConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (24 : ℝ)) (a := (5 / 2 : ℝ)) (b := commonExponent)
    (by norm_num) hcommonLtFiveHalves
  have hsmallConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (2 : ℝ)) (a := (12 / 5 : ℝ)) (b := commonExponent)
    (by norm_num) hcommonLtTwelveFifths
  have hsmoothConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := 2 + 1 / (32 * d ^ 2)) (b := commonExponent)
    (by norm_num) hcommonLtSmooth
  have hdeficientConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (1 : ℝ)) (a := 2 + 1 / d ^ 2) (b := commonExponent)
    (by norm_num) hcommonLtDeficient
  have hfinalConvert := eventually_const_mul_self_div_taoZ_rpow_le
    (C := (8 : ℝ)) (a := commonExponent) (b := finalExponent)
    (by norm_num) hcommonLtFinal
  filter_upwards [eventually_taoSlowNonTypicalFailureUnion_subset_cover n,
    hlargeLength, hlargeLengthConvert,
    eventually_card_taoShortLargePrimeFailureUnion_cast_le,
    hlargePrimeConvert,
    eventually_card_taoLongModerateFailureUnion_cast_le, hlongConvert,
    eventually_card_taoLargeSquareFailureUnion_cast_le, hsquareConvert,
    eventually_card_taoSmallPrimeFailureUnion_exponentCutoff_two_fifths_le,
    hsmallConvert,
    eventually_card_taoSlowSourceSmoothPrimeFailureUnion_le n, hsmoothConvert,
    eventually_card_taoSlowDeficientPrimeFailureUnion_le n, hdeficientConvert,
    eventually_card_taoSlowSourceHighPrimeFailureUnion_le n, hsmoothConvert,
    hfinalConvert] with x hsubset hlarge hlargeC hlargePrime hlargePrimeC
      hlong hlongC hsquare hsquareC hsmall hsmallC hsmooth hsmoothC
      hdeficient hdeficientC hhigh hhighC hfinal
  have hcardNat : (taoSlowNonTypicalFailureUnion n x).card ≤
      (taoSlowProposition65FailureCover n x).card :=
    Finset.card_le_card hsubset
  have hcover := card_taoSlowProposition65FailureCover_le n x
  have hcard : ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
      ((taoLargeLengthFailureUnion x).card : ℝ) +
      (taoShortLargePrimeFailureUnion x).card +
      (taoLongModerateFailureUnion x).card +
      (taoLargeSquareFailureUnion x).card +
      (taoSmallPrimeFailureUnion x
        (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceSmoothPrimeRange n x)).card +
      (taoDeficientPrimeFailureUnion x
        (taoTypicalSquareThreshold x)
        (taoZPowerFloor (taoSlowLowerExponent n) x)
        (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
        (taoSlowDeficientPrimeRange n x)).card +
      (taoShortSmoothPrimeFailureUnion x
        (taoSlowSourceHighPrimeRange n x)).card := by
    exact_mod_cast hcardNat.trans hcover
  have hlargeT : ((taoLargeLengthFailureUnion x).card : ℝ) ≤ T x :=
    hlarge.trans hlargeC
  have hlargePrimeT : ((taoShortLargePrimeFailureUnion x).card : ℝ) ≤ T x := by
    have hpow : (x : ℝ) ^ (199 / 200 : ℝ) =
        (x : ℝ) ^ (1 - 1 / 200 : ℝ) := by norm_num
    rw [hpow] at hlargePrime
    exact hlargePrime.trans hlargePrimeC
  have hlongT : ((taoLongModerateFailureUnion x).card : ℝ) ≤ T x :=
    hlong.trans (by simpa [T] using hlongC)
  have hsquareT : ((taoLargeSquareFailureUnion x).card : ℝ) ≤ T x :=
    hsquare.trans (by simpa [T] using hsquareC)
  have hsmallT : ((taoSmallPrimeFailureUnion x
      (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card : ℝ) ≤ T x :=
    hsmall.trans (by simpa [T] using hsmallC)
  have hsmoothT : ((taoShortSmoothPrimeFailureUnion x
      (taoSlowSourceSmoothPrimeRange n x)).card : ℝ) ≤ T x := by
    exact hsmooth.trans (by simpa [T, d] using hsmoothC)
  have hdeficientT : ((taoDeficientPrimeFailureUnion x
      (taoTypicalSquareThreshold x)
      (taoZPowerFloor (taoSlowLowerExponent n) x)
      (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
      (taoSlowDeficientPrimeRange n x)).card : ℝ) ≤ T x := by
    exact hdeficient.trans (by simpa [T, d] using hdeficientC)
  have hhighT : ((taoShortSmoothPrimeFailureUnion x
      (taoSlowSourceHighPrimeRange n x)).card : ℝ) ≤ T x := by
    exact hhigh.trans (by simpa [T, d] using hhighC)
  calc
    ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
        ((taoLargeLengthFailureUnion x).card : ℝ) +
        (taoShortLargePrimeFailureUnion x).card +
        (taoLongModerateFailureUnion x).card +
        (taoLargeSquareFailureUnion x).card +
        (taoSmallPrimeFailureUnion x
          (taoOneTermExponentCutoff (2 / 5 : ℝ) x)).card +
        (taoShortSmoothPrimeFailureUnion x
          (taoSlowSourceSmoothPrimeRange n x)).card +
        (taoDeficientPrimeFailureUnion x
          (taoTypicalSquareThreshold x)
          (taoZPowerFloor (taoSlowLowerExponent n) x)
          (taoOneTermExponentCutoff (taoSlowUpperExponent n) x)
          (taoSlowDeficientPrimeRange n x)).card +
        (taoShortSmoothPrimeFailureUnion x
          (taoSlowSourceHighPrimeRange n x)).card := hcard
    _ ≤ 8 * T x := by linarith
    _ ≤ (x : ℝ) / (taoZ x) ^ finalExponent := by
      calc
        8 * T x = 8 * (x : ℝ) / (taoZ x) ^ commonExponent := by
          dsimp only [T]
          ring
        _ ≤ (x : ℝ) / (taoZ x) ^ finalExponent := hfinal
    _ = (x : ℝ) / (taoZ x) ^
        (2 + 1 / (128 * (taoSlowCutoffDenominator n : ℝ) ^ 2)) := rfl

/-! ## Countable cutoff diagonal -/

/-- Any row selector tending to infinity makes the corresponding lower
anatomy exponent tend to one. -/
theorem tendsto_taoSlowLowerExponent_comp
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x => taoSlowLowerExponent (q x)) atTop (𝓝 1) := by
  have hdNat : Tendsto (fun x => taoSlowCutoffDenominator (q x))
      atTop atTop := by
    rw [tendsto_atTop_atTop] at hq ⊢
    intro b
    obtain ⟨a, ha⟩ := hq b
    refine ⟨a, fun x hx => ?_⟩
    unfold taoSlowCutoffDenominator
    exact (ha x hx).trans (Nat.le_add_right (q x) 10)
  have hdReal : Tendsto
      (fun x => (taoSlowCutoffDenominator (q x) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdNat
  have hquot : Tendsto
      (fun x => (2 : ℝ) / (taoSlowCutoffDenominator (q x) : ℝ))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop hdReal
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  convert hone.sub hquot using 1
  all_goals norm_num [taoSlowLowerExponent]

/-- Any row selector tending to infinity also makes the corresponding upper
distinguished-prime exponent tend to one. -/
theorem tendsto_taoSlowUpperExponent_comp
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x => taoSlowUpperExponent (q x)) atTop (𝓝 1) := by
  have hlower := tendsto_taoSlowLowerExponent_comp hq
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  convert htwo.sub hlower using 1
  all_goals norm_num [taoSlowLowerExponent, taoSlowUpperExponent]
  funext x
  ring

/-- The varying real powers underlying a slow cutoff tend to infinity. -/
theorem tendsto_taoZ_rpow_taoSlowLowerExponent_comp_atTop
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x => (taoZ x) ^ taoSlowLowerExponent (q x))
      atTop atTop := by
  have hα := tendsto_taoSlowLowerExponent_comp hq
  have hαHalf : ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) ≤ taoSlowLowerExponent (q x) :=
    hα.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hzOne : ∀ᶠ x : ℕ in atTop, 1 ≤ taoZ x :=
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hlower : ∀ᶠ x : ℕ in atTop,
      (taoZ x) ^ (1 / 2 : ℝ) ≤
        (taoZ x) ^ taoSlowLowerExponent (q x) := by
    filter_upwards [hαHalf, hzOne] with x hαx hzx
    exact Real.rpow_le_rpow_of_exponent_le hzx hαx
  exact tendsto_atTop_mono' atTop hlower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_taoZ_atTop)

/-- The varying real powers underlying the upper slow cutoff tend to
infinity as well. -/
theorem tendsto_taoZ_rpow_taoSlowUpperExponent_comp_atTop
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x => (taoZ x) ^ taoSlowUpperExponent (q x))
      atTop atTop := by
  have hα := tendsto_taoSlowUpperExponent_comp hq
  have hαHalf : ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) ≤ taoSlowUpperExponent (q x) :=
    hα.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hzOne : ∀ᶠ x : ℕ in atTop, 1 ≤ taoZ x :=
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hlower : ∀ᶠ x : ℕ in atTop,
      (taoZ x) ^ (1 / 2 : ℝ) ≤
        (taoZ x) ^ taoSlowUpperExponent (q x) := by
    filter_upwards [hαHalf, hzOne] with x hαx hzx
    exact Real.rpow_le_rpow_of_exponent_le hzx hαx
  exact tendsto_atTop_mono' atTop hlower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_taoZ_atTop)

/-- Flooring the selected varying power preserves its logarithmic exponent;
the resulting exact natural cutoff is genuinely `z^(1+o(1))`. -/
theorem tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x =>
      Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
        Real.log (taoZ x)) atTop (𝓝 1) := by
  let α : ℕ → ℝ := fun x => taoSlowLowerExponent (q x)
  let A : ℕ → ℝ := fun x => (taoZ x) ^ α x
  have hα : Tendsto α atTop (𝓝 1) := by
    simpa only [α] using tendsto_taoSlowLowerExponent_comp hq
  have hA : Tendsto A atTop atTop := by
    simpa only [A, α] using
      tendsto_taoZ_rpow_taoSlowLowerExponent_comp_atTop hq
  have hfloorRatio : Tendsto (fun x =>
      (taoZPowerFloor (α x) x : ℝ) / A x) atTop (𝓝 1) := by
    simpa only [taoZPowerFloor, A] using
      tendsto_nat_floor_div_atTop.comp hA
  have hlogRatio : Tendsto (fun x =>
      Real.log ((taoZPowerFloor (α x) x : ℝ) / A x)) atTop (𝓝 0) := by
    simpa using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        hfloorRatio)
  have hdiff : Tendsto (fun x =>
      Real.log (taoZPowerFloor (α x) x) - Real.log (A x))
      atTop (𝓝 0) := by
    apply hlogRatio.congr'
    filter_upwards [hA.eventually (eventually_gt_atTop (1 : ℝ))] with x hx
    have hfloorPos : (0 : ℝ) < taoZPowerFloor (α x) x := by
      exact_mod_cast (Nat.floor_pos.mpr hx.le : 0 < ⌊A x⌋₊)
    rw [Real.log_div hfloorPos.ne' (by positivity : A x ≠ 0)]
  have hnormalized := hdiff.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop)
  have hsum := hnormalized.add hα
  have heq : (fun x =>
      (Real.log (taoZPowerFloor (α x) x) - Real.log (A x)) /
          (Real.log ∘ taoZ) x + α x) =ᶠ[atTop]
      (fun x => Real.log (taoZPowerFloor (α x) x) /
        Real.log (taoZ x)) := by
    filter_upwards [tendsto_taoZ_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hx
    have hlogZ : Real.log (taoZ x) ≠ 0 := (Real.log_pos hx).ne'
    dsimp only [A]
    rw [Real.log_rpow (taoZ_pos x)]
    simp only [Function.comp_apply]
    field_simp [hlogZ]
    ring
  have htarget := hsum.congr' heq
  have htarget' : Tendsto (fun x =>
      Real.log (taoZPowerFloor (α x) x) / Real.log (taoZ x))
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, zero_add] using htarget
  simpa only [α] using htarget'

/-- Ceiling the selected varying upper power preserves its logarithmic
exponent, so the exact upper natural cutoff is also `z^(1+o(1))`. -/
theorem tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun x =>
      Real.log
          (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
        Real.log (taoZ x)) atTop (𝓝 1) := by
  let α : ℕ → ℝ := fun x => taoSlowUpperExponent (q x)
  let A : ℕ → ℝ := fun x => (taoZ x) ^ α x
  have hα : Tendsto α atTop (𝓝 1) := by
    simpa only [α] using tendsto_taoSlowUpperExponent_comp hq
  have hA : Tendsto A atTop atTop := by
    simpa only [A, α] using
      tendsto_taoZ_rpow_taoSlowUpperExponent_comp_atTop hq
  have hceilRatio : Tendsto (fun x =>
      (taoOneTermExponentCutoff (α x) x : ℝ) / A x)
      atTop (𝓝 1) := by
    simpa only [taoOneTermExponentCutoff, A] using
      tendsto_nat_ceil_div_atTop.comp hA
  have hlogRatio : Tendsto (fun x =>
      Real.log ((taoOneTermExponentCutoff (α x) x : ℝ) / A x))
      atTop (𝓝 0) := by
    simpa using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        hceilRatio)
  have hdiff : Tendsto (fun x =>
      Real.log (taoOneTermExponentCutoff (α x) x) - Real.log (A x))
      atTop (𝓝 0) := by
    apply hlogRatio.congr'
    filter_upwards with x
    have hceilPosNat : 0 < taoOneTermExponentCutoff (α x) x := by
      unfold taoOneTermExponentCutoff
      exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (taoZ_pos x) _)
    have hceilPos :
        (0 : ℝ) < taoOneTermExponentCutoff (α x) x := by
      exact_mod_cast hceilPosNat
    have hAPos : 0 < A x := by
      dsimp only [A]
      exact Real.rpow_pos_of_pos (taoZ_pos x) _
    rw [Real.log_div hceilPos.ne' hAPos.ne']
  have hnormalized := hdiff.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop)
  have hsum := hnormalized.add hα
  have heq : (fun x =>
      (Real.log (taoOneTermExponentCutoff (α x) x) - Real.log (A x)) /
          (Real.log ∘ taoZ) x + α x) =ᶠ[atTop]
      (fun x => Real.log (taoOneTermExponentCutoff (α x) x) /
        Real.log (taoZ x)) := by
    filter_upwards [tendsto_taoZ_atTop.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hx
    have hlogZ : Real.log (taoZ x) ≠ 0 := (Real.log_pos hx).ne'
    dsimp only [A]
    rw [Real.log_rpow (taoZ_pos x)]
    simp only [Function.comp_apply]
    field_simp [hlogZ]
    ring
  have htarget := hsum.congr' heq
  have htarget' : Tendsto (fun x =>
      Real.log (taoOneTermExponentCutoff (α x) x) / Real.log (taoZ x))
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, zero_add] using htarget
  simpa only [α] using htarget'

/-- A single slowly increasing row selector simultaneously has both source
cutoff asymptotics and the selected fixed-row Proposition 6.5 estimate. -/
theorem exists_taoProposition65_slowDiagonal :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ᶠ x : ℕ in atTop,
        ((taoSlowNonTypicalFailureUnion (q x) x).card : ℝ) ≤
          (x : ℝ) / (taoZ x) ^
            (2 + 1 /
              (128 * (taoSlowCutoffDenominator (q x) : ℝ) ^ 2)) := by
  let P : ℕ → ℕ → Prop := fun n x =>
    ((taoSlowNonTypicalFailureUnion n x).card : ℝ) ≤
      (x : ℝ) / (taoZ x) ^
        (2 + 1 / (128 * (taoSlowCutoffDenominator n : ℝ) ^ 2))
  have hP : ∀ n, ∀ᶠ x : ℕ in atTop, P n x := by
    intro n
    simpa only [P] using eventually_card_taoSlowNonTypicalFailureUnion_le n
  obtain ⟨q, hq, hselected⟩ :=
    GafniTao.exists_tendsto_nat_diagonal P hP
  exact ⟨q, hq, tendsto_log_taoSlowDiagonalCutoff_div_log_taoZ hq,
    tendsto_log_taoSlowDiagonalUpperCutoff_div_log_taoZ hq,
    by simpa only [P] using hselected⟩

/-- Source-facing consequence: for exact lower and upper `z^(1+o(1))`
natural cutoffs, the selected non-typical interval union is eventually at
most `x/z^2`. -/
theorem exists_taoProposition65_slowCutoff_union_bound :
    ∃ q : ℕ → ℕ,
      Tendsto q atTop atTop ∧
      Tendsto (fun x =>
        Real.log (taoZPowerFloor (taoSlowLowerExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      Tendsto (fun x =>
        Real.log
            (taoOneTermExponentCutoff (taoSlowUpperExponent (q x)) x) /
          Real.log (taoZ x)) atTop (𝓝 1) ∧
      ∀ᶠ x : ℕ in atTop,
        ((taoSlowNonTypicalFailureUnion (q x) x).card : ℝ) ≤
          (x : ℝ) / (taoZ x) ^ (2 : ℝ) := by
  obtain ⟨q, hq, hlowerCutoff, hupperCutoff, hbound⟩ :=
    exists_taoProposition65_slowDiagonal
  refine ⟨q, hq, hlowerCutoff, hupperCutoff, ?_⟩
  filter_upwards [hbound,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hx hz
  have hmargin : (2 : ℝ) ≤
      2 + 1 / (128 * (taoSlowCutoffDenominator (q x) : ℝ) ^ 2) := by
    have hd : (0 : ℝ) < taoSlowCutoffDenominator (q x) := by
      exact_mod_cast taoSlowCutoffDenominator_pos (q x)
    exact le_add_of_nonneg_right (by positivity)
  have hpow := Real.rpow_le_rpow_of_exponent_le hz hmargin
  exact hx.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg x)
    (Real.rpow_pos_of_pos (taoZ_pos x) _) hpow)


end

end Tao2026
