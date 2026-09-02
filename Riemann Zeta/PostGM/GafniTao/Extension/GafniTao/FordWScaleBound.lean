import GafniTao.FordScaleAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The central-band power saving in Ford's `W_j`

This file specializes the four normalized terms to the scales used in the
complete-window application.  The estimates are deliberately conservative;
their role is to produce a uniform positive Vinogradov--Korobov saving, not
to reproduce Ford's optimized numerical constants.
-/

namespace GafniTao

noncomputable section

theorem ford_one_div_fifth_scale_pow
    {x : ℝ} (hx : 0 < x) (d : ℕ) :
    1 / ((x ^ (1 / 5 : ℝ) / 2) ^ d) =
      (2 : ℝ) ^ d * x ^ (-((d : ℝ) / 5)) := by
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  rw [Real.rpow_neg hx.le]
  norm_num
  field_simp

theorem ford_tenth_scale_pow
    {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    (x ^ (1 / 10 : ℝ)) ^ d = x ^ ((d : ℝ) / 10) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

theorem ford_fifth_scale_pow
    {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    (x ^ (1 / 5 : ℝ)) ^ d = x ^ ((d : ℝ) / 5) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

theorem ford_third_scale_ratio_eq
    {x : ℝ} (hx : 0 < x) (a : ℝ) (d : ℕ) :
    (2 * x) ^ d /
        (x ^ a * (x ^ (1 / 5 : ℝ) / 2) ^ d *
          (x ^ (1 / 10 : ℝ)) ^ d) =
      (4 : ℝ) ^ d * x ^ ((7 / 10 : ℝ) * d - a) := by
  have hx0 : 0 ≤ x := hx.le
  have hpowid : x ^ d =
      x ^ a * x ^ ((d : ℝ) / 5) * x ^ ((d : ℝ) / 10) *
        x ^ ((7 / 10 : ℝ) * d - a) := by
    calc
      x ^ d = x ^ (d : ℝ) := (Real.rpow_natCast x d).symm
      _ = x ^ (a + (d : ℝ) / 5 + (d : ℝ) / 10 +
          ((7 / 10 : ℝ) * d - a)) := by (congr 1; ring)
      _ = x ^ a * x ^ ((d : ℝ) / 5) * x ^ ((d : ℝ) / 10) *
          x ^ ((7 / 10 : ℝ) * d - a) := by
        rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_add hx]
  rw [mul_pow, div_pow, ford_fifth_scale_pow hx0 d,
    ford_tenth_scale_pow hx0 d]
  have hxA : x ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hxF : x ^ ((d : ℝ) / 5) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hxT : x ^ ((d : ℝ) / 10) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hfour : ((2 : ℝ) ^ d) ^ 2 = (4 : ℝ) ^ d := by
    calc
      ((2 : ℝ) ^ d) ^ 2 = (2 : ℝ) ^ (d * 2) := (pow_mul _ _ _).symm
      _ = (2 : ℝ) ^ (2 * d) := by rw [Nat.mul_comm d 2]
      _ = ((2 : ℝ) ^ 2) ^ d := pow_mul _ _ _
      _ = (4 : ℝ) ^ d := by norm_num
  field_simp
  rw [hfour, show (((d : ℝ) * 7 - 10 * a) / 10) =
    (7 / 10 : ℝ) * d - a by ring, hpowid]
  ring

theorem ford_W_first_term_le
    {k r M : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hM : x ^ (1 / 5 : ℝ) / 2 ≤ (M : ℝ)) (hr : 1 ≤ r)
    {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    1 / ((r : ℝ) * (M : ℝ) ^ ((j : ℕ) + 1)) ≤
      (2 : ℝ) ^ k * x ^ (-(41 / 250 : ℝ) * k) := by
  let d : ℕ := (j : ℕ) + 1
  have hscalePos : 0 < x ^ (1 / 5 : ℝ) / 2 := by positivity
  have hMpos : 0 < (M : ℝ) := hscalePos.trans_le hM
  have hpow : (x ^ (1 / 5 : ℝ) / 2) ^ d ≤ (M : ℝ) ^ d :=
    pow_le_pow_left₀ hscalePos.le hM d
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : (x ^ (1 / 5 : ℝ) / 2) ^ d ≤
      (r : ℝ) * (M : ℝ) ^ d := by
    calc
      (x ^ (1 / 5 : ℝ) / 2) ^ d ≤ (M : ℝ) ^ d := hpow
      _ ≤ (r : ℝ) * (M : ℝ) ^ d := by
        nlinarith [pow_nonneg hMpos.le d]
  have hinv := one_div_le_one_div_of_le (pow_pos hscalePos d) hden
  rw [ford_one_div_fifth_scale_pow (lt_of_lt_of_le zero_lt_one hx) d] at hinv
  have hdle : d ≤ k := by dsimp [d]; omega
  have htwo : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hdle
  have hexp := fordGoodDegree_first_exponent hj
  have hxpow : x ^ (-((d : ℝ) / 5)) ≤
      x ^ (-(41 / 250 : ℝ) * k) := by
    exact Real.rpow_le_rpow_of_exponent_le hx hexp
  exact hinv.trans (mul_le_mul htwo hxpow (Real.rpow_nonneg (by linarith) _)
    (pow_nonneg (by norm_num) _))

theorem ford_W_second_term_le
    {k : ℕ} {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t)
    (htop : t ≤ x ^ ((7 / 10 : ℝ) * k))
    {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    t / (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) *
        x ^ ((j : ℕ) + 1)) ≤
      x ^ (-(3 / 25 : ℝ) * k) := by
  let d : ℕ := (j : ℕ) + 1
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hdpos : (0 : ℝ) < d := by positivity
  have hcoeff : (1 : ℝ) ≤ 2 * Real.pi * d := by
    calc
      (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * d := by
        gcongr
        · exact Real.pi_gt_three.le
        · exact_mod_cast (show 1 ≤ d by omega)
  have hxdp : 0 < x ^ d := pow_pos hxpos d
  have hdrop : t / ((2 * Real.pi * d) * x ^ d) ≤ t / x ^ d := by
    apply div_le_div_of_nonneg_left ht.le hxdp
    nlinarith
  have htopdiv : t / x ^ d ≤
      x ^ ((7 / 10 : ℝ) * k) / x ^ d := by gcongr
  have hratio : x ^ ((7 / 10 : ℝ) * k) / x ^ d =
      x ^ ((7 / 10 : ℝ) * k - d) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_sub hxpos _ _).symm
  rw [hratio] at htopdiv
  have hexp := fordGoodDegree_second_exponent hj
  have hpow := Real.rpow_le_rpow_of_exponent_le hx hexp
  exact hdrop.trans (htopdiv.trans hpow)

theorem ford_W_fourth_term_le
    {k s : ℕ} {x : ℝ} (hx : 1 ≤ x) (hs : 1 ≤ s)
    {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    1 / ((s : ℝ) * (x ^ (1 / 10 : ℝ)) ^ ((j : ℕ) + 1)) ≤
      x ^ (-(41 / 500 : ℝ) * k) := by
  let d : ℕ := (j : ℕ) + 1
  change 1 / ((s : ℝ) * (x ^ (1 / 10 : ℝ)) ^ d) ≤
    x ^ (-(41 / 500 : ℝ) * k)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsReal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hscalePos : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hscalePowPos : 0 < (x ^ (1 / 10 : ℝ)) ^ d := pow_pos hscalePos d
  have hdrop : 1 / ((s : ℝ) * (x ^ (1 / 10 : ℝ)) ^ d) ≤
      1 / (x ^ (1 / 10 : ℝ)) ^ d := by
    apply one_div_le_one_div_of_le hscalePowPos
    nlinarith [pow_nonneg hscalePos.le d]
  rw [ford_tenth_scale_pow (by linarith : 0 ≤ x) d] at hdrop ⊢
  have hinv : 1 / x ^ ((d : ℝ) / 10) = x ^ (-((d : ℝ) / 10)) := by
    simpa [one_div] using
      (Real.rpow_neg (by linarith : 0 ≤ x) ((d : ℝ) / 10)).symm
  rw [hinv] at hdrop
  have hexp := fordGoodDegree_fourth_exponent hj
  exact hdrop.trans (Real.rpow_le_rpow_of_exponent_le hx hexp)

theorem ford_eight_mul_le_two_pow {k : ℕ} (hk : 6 ≤ k) :
    8 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      omega

theorem ford_W_third_coefficient_le
    {k : ℕ} (hk : 6 ≤ k) {j : Fin k} :
    2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) *
        (4 : ℝ) ^ ((j : ℕ) + 1) ≤
      (8 : ℝ) ^ k := by
  let d : ℕ := (j : ℕ) + 1
  have hd : d ≤ k := by dsimp [d]; omega
  have hlinearNat : 8 * k ≤ 2 ^ k := ford_eight_mul_le_two_pow hk
  have hlinear : (8 : ℝ) * k ≤ (2 : ℝ) ^ k := by exact_mod_cast hlinearNat
  have hpiD : 2 * Real.pi * (d : ℝ) ≤ (2 : ℝ) ^ k := by
    calc
      2 * Real.pi * (d : ℝ) ≤ 8 * (d : ℝ) := by
        have hpi := Real.pi_lt_four.le
        nlinarith [show (0 : ℝ) ≤ d by positivity]
      _ ≤ 8 * (k : ℝ) := by gcongr
      _ ≤ (2 : ℝ) ^ k := hlinear
  have hfour : (4 : ℝ) ^ d ≤ (4 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hd
  calc
    2 * Real.pi * (d : ℝ) * (4 : ℝ) ^ d ≤
        (2 : ℝ) ^ k * (4 : ℝ) ^ k := by
      exact mul_le_mul hpiD hfour (pow_nonneg (by norm_num) _)
        (by positivity)
    _ = (8 : ℝ) ^ k := by rw [← mul_pow]; norm_num

theorem ford_W_third_term_le
    {k r s M : ℕ} {x t : ℝ} (hk : 6 ≤ k) (hx : 1 ≤ x)
    (ht : 0 < t)
    (hbottom : x ^ ((69 / 100 : ℝ) * k) ≤ t)
    (hM : x ^ (1 / 5 : ℝ) / 2 ≤ (M : ℝ))
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) *
        (2 * x) ^ ((j : ℕ) + 1)) /
        ((r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ ((j : ℕ) + 1) *
          (x ^ (1 / 10 : ℝ)) ^ ((j : ℕ) + 1)) ≤
      (8 : ℝ) ^ k * x ^ (-(81 / 1000 : ℝ) * k) := by
  let d : ℕ := (j : ℕ) + 1
  change (2 * Real.pi * (d : ℝ) * (2 * x) ^ d) /
      ((r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ d *
        (x ^ (1 / 10 : ℝ)) ^ d) ≤
    (8 : ℝ) ^ k * x ^ (-(81 / 1000 : ℝ) * k)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hscalePos : 0 < x ^ (1 / 5 : ℝ) / 2 := by positivity
  have hMpos : 0 < (M : ℝ) := hscalePos.trans_le hM
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  let a : ℝ := (69 / 100 : ℝ) * k
  let D : ℝ := x ^ a * (x ^ (1 / 5 : ℝ) / 2) ^ d *
    (x ^ (1 / 10 : ℝ)) ^ d
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hMpow : (x ^ (1 / 5 : ℝ) / 2) ^ d ≤ (M : ℝ) ^ d :=
    pow_le_pow_left₀ hscalePos.le hM d
  have hden : D ≤ (r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ d *
      (x ^ (1 / 10 : ℝ)) ^ d := by
    dsimp [D, a]
    calc
      x ^ ((69 / 100 : ℝ) * k) * (x ^ (1 / 5 : ℝ) / 2) ^ d *
          (x ^ (1 / 10 : ℝ)) ^ d ≤
        t * (M : ℝ) ^ d * (x ^ (1 / 10 : ℝ)) ^ d := by gcongr
      _ ≤ ((r : ℝ) * (s : ℝ)) * t * (M : ℝ) ^ d *
          (x ^ (1 / 10 : ℝ)) ^ d := by
        have hrs : (1 : ℝ) ≤ (r : ℝ) * s := by nlinarith
        have hrest : 0 ≤ t * (M : ℝ) ^ d *
            (x ^ (1 / 10 : ℝ)) ^ d := by positivity
        nlinarith
      _ = (r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ d *
          (x ^ (1 / 10 : ℝ)) ^ d := by ring
  have hnum : 0 ≤ 2 * Real.pi * (d : ℝ) * (2 * x) ^ d := by positivity
  have hdrop :
      (2 * Real.pi * (d : ℝ) * (2 * x) ^ d) /
          ((r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ d *
            (x ^ (1 / 10 : ℝ)) ^ d) ≤
        (2 * Real.pi * (d : ℝ) * (2 * x) ^ d) / D :=
    div_le_div_of_nonneg_left hnum hDpos hden
  have hrewrite :
      (2 * Real.pi * (d : ℝ) * (2 * x) ^ d) / D =
        (2 * Real.pi * (d : ℝ) * (4 : ℝ) ^ d) *
          x ^ ((7 / 10 : ℝ) * d - a) := by
    dsimp [D]
    rw [show (2 * Real.pi * (d : ℝ) * (2 * x) ^ d) /
        (x ^ a * (x ^ (1 / 5 : ℝ) / 2) ^ d *
          (x ^ (1 / 10 : ℝ)) ^ d) =
        (2 * Real.pi * (d : ℝ)) *
          ((2 * x) ^ d /
            (x ^ a * (x ^ (1 / 5 : ℝ) / 2) ^ d *
              (x ^ (1 / 10 : ℝ)) ^ d)) by ring,
      ford_third_scale_ratio_eq hxpos a d]
    ring
  rw [hrewrite] at hdrop
  have hcoeff := ford_W_third_coefficient_le hk (j := j)
  have hexp := fordGoodDegree_third_exponent hj
  have hxpow : x ^ ((7 / 10 : ℝ) * d - a) ≤
      x ^ (-(81 / 1000 : ℝ) * k) := by
    exact Real.rpow_le_rpow_of_exponent_le hx (by simpa [a, d] using hexp)
  exact hdrop.trans (mul_le_mul hcoeff hxpow
    (Real.rpow_nonneg (by linarith) _) (by positivity))

/-- A literal common envelope for all four normalized terms on the good
degree band. -/
def fordWGoodEnvelope (k : ℕ) (x : ℝ) : ℝ :=
  ((2 : ℝ) ^ k + 1 + (8 : ℝ) ^ k + 1) *
    x ^ (-(2 / 25 : ℝ) * k)

theorem fordWNormalizedFactor_good_le
    {k r s M : ℕ} {x t : ℝ} (hk : 6 ≤ k) (hx : 1 ≤ x)
    (ht : 0 < t)
    (hbottom : x ^ ((69 / 100 : ℝ) * k) ≤ t)
    (htop : t ≤ x ^ ((7 / 10 : ℝ) * k))
    (hM : x ^ (1 / 5 : ℝ) / 2 ≤ (M : ℝ))
    (hr : 1 ≤ r) (hs : 1 ≤ s)
    {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    fordWNormalizedFactor s (x ^ (1 / 10 : ℝ)) r M x t j ≤
      fordWGoodEnvelope k x := by
  let d : ℕ := (j : ℕ) + 1
  have h₁ := ford_W_first_term_le hx hM hr hj
  have h₂ := ford_W_second_term_le hx ht htop hj
  have h₃ := ford_W_third_term_le hk hx ht hbottom hM hr hs hj
  have h₄ := ford_W_fourth_term_le hx hs hj
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hbase :
      x ^ (-(41 / 250 : ℝ) * k) ≤ x ^ (-(2 / 25 : ℝ) * k) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have hsecond :
      x ^ (-(3 / 25 : ℝ) * k) ≤ x ^ (-(2 / 25 : ℝ) * k) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have hthird :
      x ^ (-(81 / 1000 : ℝ) * k) ≤ x ^ (-(2 / 25 : ℝ) * k) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have hfourth :
      x ^ (-(41 / 500 : ℝ) * k) ≤ x ^ (-(2 / 25 : ℝ) * k) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  unfold fordWNormalizedFactor fordWGoodEnvelope
  calc
    1 / ((r : ℝ) * (M : ℝ) ^ d) +
          t / (2 * Real.pi * (d : ℝ) * x ^ d) +
          (2 * Real.pi * (d : ℝ) * (2 * x) ^ d) /
            ((r : ℝ) * (s : ℝ) * t * (M : ℝ) ^ d *
              (x ^ (1 / 10 : ℝ)) ^ d) +
          1 / ((s : ℝ) * (x ^ (1 / 10 : ℝ)) ^ d) ≤
        (2 : ℝ) ^ k * x ^ (-(41 / 250 : ℝ) * k) +
          x ^ (-(3 / 25 : ℝ) * k) +
          (8 : ℝ) ^ k * x ^ (-(81 / 1000 : ℝ) * k) +
          x ^ (-(41 / 500 : ℝ) * k) := by
      exact add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ ≤ (2 : ℝ) ^ k * x ^ (-(2 / 25 : ℝ) * k) +
          x ^ (-(2 / 25 : ℝ) * k) +
          (8 : ℝ) ^ k * x ^ (-(2 / 25 : ℝ) * k) +
          x ^ (-(2 / 25 : ℝ) * k) := by gcongr
    _ = ((2 : ℝ) ^ k + 1 + (8 : ℝ) ^ k + 1) *
          x ^ (-(2 / 25 : ℝ) * k) := by ring

theorem fordLemma51WReal_scaled_prod_le
    {k N : ℕ} {t : ℝ} (hk : fordCoefficientKThreshold ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    (∏ j : FordLemma51DegreeWindow k 1 k,
        fordLemma51WReal (2 * k ^ 2) ((N : ℝ) ^ (1 / 10 : ℝ))
          (2 * k ^ 2) ⌊(N : ℝ) ^ (1 / 5 : ℝ)⌋₊ N t j.1) ≤
      (2 * ((2 * k ^ 2 : ℕ) : ℝ)) ^ k *
        ((N : ℝ) ^ (1 / 10 : ℝ)) ^ fordVinogradovKappa k *
        (fordWGoodEnvelope k N) ^ (fordGoodDegreeSet k).card := by
  have hk1000 : 1000 ≤ k := fordCoefficientKThreshold_ge_thousand.trans hk
  have hk6 : 6 ≤ k := by omega
  have hNgt : 1 < N := by omega
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨_hM₁two, _hM₂two, hfloor, hfloorOne, _hQOne,
      _hM₁top, _hM₂top, _hprodTop⟩ :=
    ford_basic_scale_data (x := (N : ℝ)) (by exact_mod_cast hN)
  obtain ⟨htBottom, htTop⟩ :=
    ford_lambda_band_t_bounds hNgt ht hlower hupper
  have hrsOne : 1 ≤ 2 * k ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  apply fordLemma51WReal_full_prod_le
    (hs := by positivity) (hM₂ := by positivity) (hr := by positivity)
    (hM := hfloorOne) (hN := by positivity) (ht := ht)
  intro j hj
  exact fordWNormalizedFactor_good_le hk6 hx ht htBottom htTop hfloor
    hrsOne hrsOne hj

#print axioms ford_one_div_fifth_scale_pow
#print axioms ford_tenth_scale_pow
#print axioms ford_W_first_term_le
#print axioms ford_W_second_term_le
#print axioms ford_W_fourth_term_le
#print axioms ford_W_third_term_le
#print axioms fordWNormalizedFactor_good_le
#print axioms fordLemma51WReal_scaled_prod_le

end

end GafniTao
