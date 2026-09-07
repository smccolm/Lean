import RiemannZeta.GuthMaynard.HughesYoungEquation96LogSummability
import RiemannZeta.GuthMaynard.HughesYoungLemma61

open Complex Finset Metric Set
open scoped BigOperators Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Differentiating the complete Hughes--Young equation-(96) series

The two logarithms in the DFI equation-(27) main term are obtained by
differentiating equation (96) in its three exponent variables.  The
termwise identities alone do not justify this operation.  This file supplies
the missing positive-index identities and the locally uniform majorants used
to differentiate the complete absolutely convergent series.
-/

theorem hasDerivAt_hughesYoungEquation96PositiveTerm_a
    (h k : ℕ) (a b c : ℂ) (y : ℕ+ × ℕ+) :
    HasDerivAt
      (fun z => hughesYoungEquation96PositiveTerm h k z b c y)
      (hughesYoungEquation96PositiveTerm h k a b c y *
        (Complex.log (Nat.gcd h (y.1 : ℕ) : ℂ) -
          Complex.log ((y.1 : ℕ) : ℂ))) a := by
  let r : ℕ := (y.2 : ℕ) - 1
  let l : ℕ := (y.1 : ℕ) - 1
  have hr : r + 1 = (y.2 : ℕ) := by
    dsimp only [r]
    exact Nat.sub_add_cancel y.2.2
  have hl : l + 1 = (y.1 : ℕ) := by
    dsimp only [l]
    exact Nat.sub_add_cancel y.1.2
  have hlC : (l : ℂ) + 1 = ((y.1 : ℕ) : ℂ) := by exact_mod_cast hl
  have hderiv := hasDerivAt_hughesYoungEquation96Term_a h k a b c r l
  simpa [hughesYoungEquation96PositiveTerm, hughesYoungEquation96Term,
    hughesYoungEquation96LogA, hr, hl, hlC] using hderiv

theorem hasDerivAt_hughesYoungEquation96PositiveTerm_b
    (h k : ℕ) (a b c : ℂ) (y : ℕ+ × ℕ+) :
    HasDerivAt
      (fun z => hughesYoungEquation96PositiveTerm h k a z c y)
      (hughesYoungEquation96PositiveTerm h k a b c y *
        (Complex.log (Nat.gcd k (y.1 : ℕ) : ℂ) -
          Complex.log ((y.1 : ℕ) : ℂ))) b := by
  let r : ℕ := (y.2 : ℕ) - 1
  let l : ℕ := (y.1 : ℕ) - 1
  have hr : r + 1 = (y.2 : ℕ) := by
    dsimp only [r]
    exact Nat.sub_add_cancel y.2.2
  have hl : l + 1 = (y.1 : ℕ) := by
    dsimp only [l]
    exact Nat.sub_add_cancel y.1.2
  have hlC : (l : ℂ) + 1 = ((y.1 : ℕ) : ℂ) := by exact_mod_cast hl
  have hderiv := hasDerivAt_hughesYoungEquation96Term_b h k a b c r l
  simpa [hughesYoungEquation96PositiveTerm, hughesYoungEquation96Term,
    hughesYoungEquation96LogB, hr, hl, hlC] using hderiv

theorem hasDerivAt_hughesYoungEquation96PositiveTerm_c
    (h k : ℕ) (a b c : ℂ) (y : ℕ+ × ℕ+) :
    HasDerivAt
      (fun z => hughesYoungEquation96PositiveTerm h k a b z y)
      (-(hughesYoungEquation96PositiveTerm h k a b c y *
        Complex.log ((y.2 : ℕ) : ℂ))) c := by
  let r : ℕ := (y.2 : ℕ) - 1
  let l : ℕ := (y.1 : ℕ) - 1
  have hr : r + 1 = (y.2 : ℕ) := by
    dsimp only [r]
    exact Nat.sub_add_cancel y.2.2
  have hl : l + 1 = (y.1 : ℕ) := by
    dsimp only [l]
    exact Nat.sub_add_cancel y.1.2
  have hrC : (r : ℂ) + 1 = ((y.2 : ℕ) : ℂ) := by exact_mod_cast hr
  have hderiv := hasDerivAt_hughesYoungEquation96Term_c h k a b c r l
  simpa [hughesYoungEquation96PositiveTerm, hughesYoungEquation96Term,
    hughesYoungEquation96LogR, hr, hl, hrC] using hderiv

theorem hughesYoungCommonDivisorMajorant_mono
    {A₀ A C₀ C : ℝ} (hA : A₀ ≤ A) (hC : C₀ ≤ C)
    (y : ℕ+ × ℕ+) :
    hughesYoungCommonDivisorMajorant A C y ≤
      hughesYoungCommonDivisorMajorant A₀ C₀ y := by
  have hl1 : (1 : ℝ) ≤ (y.1 : ℕ) := by exact_mod_cast y.1.2
  have hr1 : (1 : ℝ) ≤ (y.2 : ℕ) := by exact_mod_cast y.2.2
  unfold hughesYoungCommonDivisorMajorant
  apply Finset.sum_le_sum
  intro d _hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hlA : (((y.1 : ℕ) : ℝ) ^ A₀) ≤
      ((y.1 : ℕ) : ℝ) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hl1 hA
  have hrC : (((y.2 : ℕ) : ℝ) ^ (1 + C₀)) ≤
      ((y.2 : ℕ) : ℝ) ^ (1 + C) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hleft : (d : ℝ) / (((y.1 : ℕ) : ℝ) ^ A) ≤
      (d : ℝ) / (((y.1 : ℕ) : ℝ) ^ A₀) :=
    div_le_div_of_nonneg_left hd0 (by positivity) hlA
  calc
    (d : ℝ) / (((y.1 : ℕ) : ℝ) ^ A) /
        (((y.2 : ℕ) : ℝ) ^ (1 + C)) ≤
      (d : ℝ) / (((y.1 : ℕ) : ℝ) ^ A₀) /
        (((y.2 : ℕ) : ℝ) ^ (1 + C)) := by
          exact div_le_div_of_nonneg_right hleft (by positivity)
    _ ≤ (d : ℝ) / (((y.1 : ℕ) : ℝ) ^ A₀) /
        (((y.2 : ℕ) : ℝ) ^ (1 + C₀)) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hrC

theorem hughesYoungGCDCPowBound_mono_re
    {h : ℕ} {a b : ℂ} (hab : a.re ≤ b.re) :
    hughesYoungGCDCPowBound h a ≤ hughesYoungGCDCPowBound h b := by
  unfold hughesYoungGCDCPowBound
  apply Finset.sum_le_sum
  intro d hd
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPos
  rw [Complex.norm_natCast_cpow_of_pos hdPos,
    Complex.norm_natCast_cpow_of_pos hdPos]
  exact Real.rpow_le_rpow_of_exponent_le hdOne hab

theorem hughesYoungEquation96_ball_re_bounds
    {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1 / 8 : ℝ)) :
    (7 / 8 : ℝ) ≤ z.re ∧ z.re ≤ 2 := by
  have hdist : ‖z - 1‖ < (1 / 8 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq] using hz
  have hre := Complex.abs_re_le_norm (z - 1)
  simp only [sub_re, one_re] at hre
  constructor <;> linarith [le_abs_self (z.re - 1), neg_abs_le (z.re - 1)]

theorem one_le_pnat_rpow
    (x : ℕ+) {a : ℝ} (ha : 0 ≤ a) :
    1 ≤ (((x : ℕ) : ℝ) ^ a) := by
  apply Real.one_le_rpow
  · exact_mod_cast x.2
  · exact ha

theorem norm_hughesYoungEquation96PositiveTerm_a_deriv_le_majorant
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1 / 8 : ℝ))
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k z 1 2 y *
        (Complex.log (Nat.gcd h (y.1 : ℕ) : ℂ) -
          Complex.log ((y.1 : ℕ) : ℂ))‖ ≤
      (16 * (hughesYoungGCDCPowBound h 2 *
        hughesYoungGCDCPowBound k 2)) *
        hughesYoungPositivePairMajorant (13 / 8) (7 / 8) y := by
  have hzBounds := hughesYoungEquation96_ball_re_bounds hz
  have hterm :
      ‖hughesYoungEquation96PositiveTerm h k z 1 2 y‖ ≤
        (hughesYoungGCDCPowBound h z *
          hughesYoungGCDCPowBound k 1) *
            hughesYoungCommonDivisorMajorant (z + 1).re 1 y := by
    convert norm_hughesYoungEquation96PositiveTerm_le
      hh hk z 1 (1 : ℂ) y using 1
    all_goals norm_num
  have hKh := hughesYoungGCDCPowBound_mono_re
    (h := h) (a := z) (b := (2 : ℂ)) hzBounds.2
  have hKk : hughesYoungGCDCPowBound k (1 : ℂ) ≤
      hughesYoungGCDCPowBound k (2 : ℂ) :=
    hughesYoungGCDCPowBound_mono_re
      (h := k) (a := (1 : ℂ)) (b := (2 : ℂ)) (by norm_num)
  have hM := hughesYoungCommonDivisorMajorant_mono
    (A₀ := 7 / 4) (C₀ := 1) (A := (z + 1).re) (C := 1)
    (by simp only [add_re, one_re]; linarith [hzBounds.1]) (le_rfl) y
  have hlog := norm_hughesYoungEquation96PositiveLogA_le h y.1
  have hlogPow := Real.log_natCast_le_rpow_div (y.1 : ℕ)
    (show (0 : ℝ) < 1 / 8 by norm_num)
  have hlog' :
      ‖Complex.log (Nat.gcd h (y.1 : ℕ) : ℂ) -
          Complex.log ((y.1 : ℕ) : ℂ)‖ ≤
        16 * (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
    calc
      _ ≤ 2 * Real.log ((y.1 : ℕ) : ℝ) := hlog
      _ ≤ 16 * (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
        have := hlogPow
        norm_num [div_eq_mul_inv] at this ⊢
        linarith
  have hpair0 : 0 ≤ hughesYoungCommonDivisorMajorant (7 / 4) 1 y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hpowR : 1 ≤ (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) :=
    one_le_pnat_rpow y.2 (by norm_num)
  have hpowL0 : 0 ≤ (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
    positivity
  have hscale :
      (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
          hughesYoungCommonDivisorMajorant (7 / 4) 1 y ≤
        ((((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) *
            hughesYoungCommonDivisorMajorant (7 / 4) 1 y := by
    have hpowmul :
        (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ≤
          (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
            (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
      calc
        _ = (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpowR hpowL0
    exact mul_le_mul_of_nonneg_right hpowmul hpair0
  have hKz0 : 0 ≤ hughesYoungGCDCPowBound h z := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKk10 : 0 ≤ hughesYoungGCDCPowBound k (1 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKh20 : 0 ≤ hughesYoungGCDCPowBound h (2 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKk20 : 0 ≤ hughesYoungGCDCPowBound k (2 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKprod :
      hughesYoungGCDCPowBound h z * hughesYoungGCDCPowBound k 1 ≤
        hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2 :=
    mul_le_mul hKh hKk hKk10 hKh20
  have hMsource0 :
      0 ≤ hughesYoungCommonDivisorMajorant (z + 1).re 1 y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hshift := mul_rpow_commonDivisorMajorant_eq
    (7 / 4) 1 (1 / 8) y
  rw [norm_mul]
  calc
    ‖hughesYoungEquation96PositiveTerm h k z 1 2 y‖ *
        ‖Complex.log (Nat.gcd h (y.1 : ℕ) : ℂ) -
          Complex.log ((y.1 : ℕ) : ℂ)‖ ≤
      ((hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
          hughesYoungCommonDivisorMajorant (7 / 4) 1 y) *
        (16 * (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) := by
      gcongr
      exact hterm.trans (mul_le_mul
        hKprod hM hMsource0
        (mul_nonneg hKh20 hKk20))
    _ ≤ (16 * (hughesYoungGCDCPowBound h 2 *
          hughesYoungGCDCPowBound k 2)) *
        (((((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) *
            hughesYoungCommonDivisorMajorant (7 / 4) 1 y) := by
      calc
        _ = 16 *
            (hughesYoungGCDCPowBound h 2 *
              hughesYoungGCDCPowBound k 2) *
            ((((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
              hughesYoungCommonDivisorMajorant (7 / 4) 1 y) := by ring
        _ ≤ 16 *
            (hughesYoungGCDCPowBound h 2 *
              hughesYoungGCDCPowBound k 2) *
            (((((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
              (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) *
                hughesYoungCommonDivisorMajorant (7 / 4) 1 y) := by
          gcongr
    _ = (16 * (hughesYoungGCDCPowBound h 2 *
          hughesYoungGCDCPowBound k 2)) *
        hughesYoungCommonDivisorMajorant (13 / 8) (7 / 8) y := by
      rw [hshift]
      norm_num
    _ ≤ _ := by
      gcongr
      exact hughesYoungCommonDivisorMajorant_le_pairMajorant
        (show (1 : ℝ) < 13 / 8 by norm_num)
        (show (0 : ℝ) < 7 / 8 by norm_num) y

theorem hughesYoungEquation96PositiveTerm_swap
    (h k : ℕ) (a b c : ℂ) (y : ℕ+ × ℕ+) :
    hughesYoungEquation96PositiveTerm h k a b c y =
      hughesYoungEquation96PositiveTerm k h b a c y := by
  unfold hughesYoungEquation96PositiveTerm
  rw [add_comm a b]
  ring

theorem norm_hughesYoungEquation96PositiveTerm_b_deriv_le_majorant
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1 / 8 : ℝ))
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 z 2 y *
        (Complex.log (Nat.gcd k (y.1 : ℕ) : ℂ) -
          Complex.log ((y.1 : ℕ) : ℂ))‖ ≤
      (16 * (hughesYoungGCDCPowBound h 2 *
        hughesYoungGCDCPowBound k 2)) *
        hughesYoungPositivePairMajorant (13 / 8) (7 / 8) y := by
  rw [hughesYoungEquation96PositiveTerm_swap h k 1 z 2 y]
  have hbound :=
    norm_hughesYoungEquation96PositiveTerm_a_deriv_le_majorant hk hh hz y
  simpa only [mul_comm
    (hughesYoungGCDCPowBound k 2) (hughesYoungGCDCPowBound h 2)] using hbound

theorem hughesYoungEquation96_ball_two_re_bounds
    {z : ℂ} (hz : z ∈ Metric.ball (2 : ℂ) (1 / 8 : ℝ)) :
    (15 / 8 : ℝ) ≤ z.re ∧ z.re ≤ 3 := by
  have hdist : ‖z - 2‖ < (1 / 8 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq] using hz
  have hre := Complex.abs_re_le_norm (z - 2)
  norm_num at hre
  constructor <;> linarith [le_abs_self (z.re - 2), neg_abs_le (z.re - 2)]

theorem norm_hughesYoungEquation96PositiveTerm_c_deriv_le_majorant
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {z : ℂ} (hz : z ∈ Metric.ball (2 : ℂ) (1 / 8 : ℝ))
    (y : ℕ+ × ℕ+) :
    ‖-(hughesYoungEquation96PositiveTerm h k 1 1 z y *
        Complex.log ((y.2 : ℕ) : ℂ))‖ ≤
      (8 * (hughesYoungGCDCPowBound h 2 *
        hughesYoungGCDCPowBound k 2)) *
        hughesYoungPositivePairMajorant (15 / 8) (3 / 4) y := by
  have hzBounds := hughesYoungEquation96_ball_two_re_bounds hz
  have hterm :
      ‖hughesYoungEquation96PositiveTerm h k 1 1 z y‖ ≤
        (hughesYoungGCDCPowBound h 1 *
          hughesYoungGCDCPowBound k 1) *
            hughesYoungCommonDivisorMajorant 2 (z - 1).re y := by
    convert norm_hughesYoungEquation96PositiveTerm_le
      hh hk 1 1 (z - 1) y using 1
    all_goals norm_num
  have hKh : hughesYoungGCDCPowBound h (1 : ℂ) ≤
      hughesYoungGCDCPowBound h (2 : ℂ) :=
    hughesYoungGCDCPowBound_mono_re
      (h := h) (a := (1 : ℂ)) (b := (2 : ℂ)) (by norm_num)
  have hKk : hughesYoungGCDCPowBound k (1 : ℂ) ≤
      hughesYoungGCDCPowBound k (2 : ℂ) :=
    hughesYoungGCDCPowBound_mono_re
      (h := k) (a := (1 : ℂ)) (b := (2 : ℂ)) (by norm_num)
  have hM := hughesYoungCommonDivisorMajorant_mono
    (A₀ := 2) (C₀ := 7 / 8) (A := 2) (C := (z - 1).re)
    (le_rfl) (by simp only [sub_re, one_re]; linarith [hzBounds.1]) y
  have hlogPow := Real.log_natCast_le_rpow_div (y.2 : ℕ)
    (show (0 : ℝ) < 1 / 8 by norm_num)
  have hlogNonneg : 0 ≤ Real.log ((y.2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast y.2.2)
  have hlog :
      ‖Complex.log ((y.2 : ℕ) : ℂ)‖ ≤
        8 * (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogNonneg]
    norm_num [div_eq_mul_inv] at hlogPow ⊢
    simpa only [mul_comm] using hlogPow
  have hK10 : 0 ≤ hughesYoungGCDCPowBound h (1 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKk10 : 0 ≤ hughesYoungGCDCPowBound k (1 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKh20 : 0 ≤ hughesYoungGCDCPowBound h (2 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKk20 : 0 ≤ hughesYoungGCDCPowBound k (2 : ℂ) := by
    unfold hughesYoungGCDCPowBound
    positivity
  have hKprod :
      hughesYoungGCDCPowBound h 1 * hughesYoungGCDCPowBound k 1 ≤
        hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2 :=
    mul_le_mul hKh hKk hKk10 hKh20
  have hMsource0 :
      0 ≤ hughesYoungCommonDivisorMajorant 2 (z - 1).re y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hMtarget0 :
      0 ≤ hughesYoungCommonDivisorMajorant 2 (7 / 8) y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hpowL : 1 ≤ (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) :=
    one_le_pnat_rpow y.1 (by norm_num)
  have hpowR0 : 0 ≤ (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
    positivity
  have hscale :
      (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
          hughesYoungCommonDivisorMajorant 2 (7 / 8) y ≤
        ((((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) *
            hughesYoungCommonDivisorMajorant 2 (7 / 8) y := by
    have hpowmul :
        (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ≤
          (((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
            (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
      calc
        _ = 1 * (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpowL hpowR0
    exact mul_le_mul_of_nonneg_right hpowmul hMtarget0
  have hshift := mul_rpow_commonDivisorMajorant_eq
    2 (7 / 8) (1 / 8) y
  rw [norm_neg, norm_mul]
  calc
    ‖hughesYoungEquation96PositiveTerm h k 1 1 z y‖ *
        ‖Complex.log ((y.2 : ℕ) : ℂ)‖ ≤
      ((hughesYoungGCDCPowBound h 2 * hughesYoungGCDCPowBound k 2) *
          hughesYoungCommonDivisorMajorant 2 (7 / 8) y) *
        (8 * (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) := by
      gcongr
      exact hterm.trans (mul_le_mul hKprod hM hMsource0
        (mul_nonneg hKh20 hKk20))
    _ ≤ (8 * (hughesYoungGCDCPowBound h 2 *
          hughesYoungGCDCPowBound k 2)) *
        (((((y.1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
          (((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ))) *
            hughesYoungCommonDivisorMajorant 2 (7 / 8) y) := by
      calc
        _ = 8 * (hughesYoungGCDCPowBound h 2 *
              hughesYoungGCDCPowBound k 2) *
            ((((y.2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) *
              hughesYoungCommonDivisorMajorant 2 (7 / 8) y) := by ring
        _ ≤ _ := by gcongr
    _ = (8 * (hughesYoungGCDCPowBound h 2 *
          hughesYoungGCDCPowBound k 2)) *
        hughesYoungCommonDivisorMajorant (15 / 8) (3 / 4) y := by
      rw [hshift]
      norm_num
    _ ≤ _ := by
      gcongr
      exact hughesYoungCommonDivisorMajorant_le_pairMajorant
        (show (1 : ℝ) < 15 / 8 by norm_num)
        (show (0 : ℝ) < 3 / 4 by norm_num) y

theorem hasDerivAt_tsum_hughesYoungEquation96PositiveTerm_a
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    HasDerivAt
      (fun z : ℂ => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k z 1 2 y)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          (Complex.log (Nat.gcd h (y.1 : ℕ) : ℂ) -
            Complex.log ((y.1 : ℕ) : ℂ))) 1 := by
  let K : ℝ := 16 * (hughesYoungGCDCPowBound h 2 *
    hughesYoungGCDCPowBound k 2)
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    K * hughesYoungPositivePairMajorant (13 / 8) (7 / 8) y
  have hu : Summable u :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 13 / 8 by norm_num)
      (show (0 : ℝ) < 7 / 8 by norm_num)).mul_left K
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1 2 y) := by
    convert summable_hughesYoungEquation96PositiveTerm
      hh hk (a := (1 : ℂ)) (b := (1 : ℂ)) (c := (1 : ℂ))
        (by norm_num) (by norm_num) using 1
    all_goals norm_num
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y z _hz => hasDerivAt_hughesYoungEquation96PositiveTerm_a h k z 1 2 y)
    (fun y z hz => by
      simpa only [u, K] using
        norm_hughesYoungEquation96PositiveTerm_a_deriv_le_majorant hh hk hz y)
    (by simp) hpoint (by simp)

theorem hasDerivAt_tsum_hughesYoungEquation96PositiveTerm_b
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    HasDerivAt
      (fun z : ℂ => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 z 2 y)
      (∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          (Complex.log (Nat.gcd k (y.1 : ℕ) : ℂ) -
            Complex.log ((y.1 : ℕ) : ℂ))) 1 := by
  let K : ℝ := 16 * (hughesYoungGCDCPowBound h 2 *
    hughesYoungGCDCPowBound k 2)
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    K * hughesYoungPositivePairMajorant (13 / 8) (7 / 8) y
  have hu : Summable u :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 13 / 8 by norm_num)
      (show (0 : ℝ) < 7 / 8 by norm_num)).mul_left K
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1 2 y) := by
    convert summable_hughesYoungEquation96PositiveTerm
      hh hk (a := (1 : ℂ)) (b := (1 : ℂ)) (c := (1 : ℂ))
        (by norm_num) (by norm_num) using 1
    all_goals norm_num
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y z _hz => hasDerivAt_hughesYoungEquation96PositiveTerm_b h k 1 z 2 y)
    (fun y z hz => by
      simpa only [u, K] using
        norm_hughesYoungEquation96PositiveTerm_b_deriv_le_majorant hh hk hz y)
    (by simp) hpoint (by simp)

theorem hasDerivAt_tsum_hughesYoungEquation96PositiveTerm_c
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    HasDerivAt
      (fun z : ℂ => ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 z y)
      (∑' y : ℕ+ × ℕ+,
        -(hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          Complex.log ((y.2 : ℕ) : ℂ))) 2 := by
  let K : ℝ := 8 * (hughesYoungGCDCPowBound h 2 *
    hughesYoungGCDCPowBound k 2)
  let u : ℕ+ × ℕ+ → ℝ := fun y =>
    K * hughesYoungPositivePairMajorant (15 / 8) (3 / 4) y
  have hu : Summable u :=
    (summable_hughesYoungPositivePairMajorant
      (show (1 : ℝ) < 15 / 8 by norm_num)
      (show (0 : ℝ) < 3 / 4 by norm_num)).mul_left K
  have hpoint : Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1 2 y) := by
    convert summable_hughesYoungEquation96PositiveTerm
      hh hk (a := (1 : ℂ)) (b := (1 : ℂ)) (c := (1 : ℂ))
        (by norm_num) (by norm_num) using 1
    all_goals norm_num
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball
    (fun y z _hz => hasDerivAt_hughesYoungEquation96PositiveTerm_c h k 1 1 z y)
    (fun y z hz => by
      simpa only [u, K] using
        norm_hughesYoungEquation96PositiveTerm_c_deriv_le_majorant hh hk hz y)
    (by simp) hpoint (by simp)

end RiemannZeta.GuthMaynard
