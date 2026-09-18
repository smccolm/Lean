import Tao2026.SmoothNumberSaddleHTContourWidth
import GafniTao.SharpPerronTermBounds
import GafniTao.SharpPerronEndpoint

/-!
# Sharp-Perron truncation majorant for the HT contour

The norm of the shifted coefficient at `s=1-beta+i*t` is computed exactly.
When it is multiplied by the Perron power on the selected right line, all
`beta` dependence factors out as `y^(beta-1)` and the remaining exponent is
the frozen optimized sharp-Perron abscissa `1+1/log y`.

Using the frozen lower-side, endpoint, and upper-side kernel bounds, this
module constructs a nonnegative summable scalar majorant for every term of
the shifted truncation series.  The final theorem bounds the norm of the
complete truncation error by `y^(beta-1)` times the majorant's `tsum`.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

theorem norm_smoothSaddleHTShiftedMangoldtCoefficient_sourceExponent
    {n : ℕ} (hn : 1 ≤ n) (beta t : ℝ) :
    ‖smoothSaddleHTShiftedMangoldtCoefficient
        (smoothSaddleHTSourceExponent beta t) n‖ =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold smoothSaddleHTShiftedMangoldtCoefficient
  rw [LSeries.term_of_ne_zero hn0, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  congr 1
  change ‖((n : ℝ) : ℂ) ^ smoothSaddleHTSourceExponent beta t‖ =
    (n : ℝ) ^ (1 - beta)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
  simp

theorem smoothSaddleHTShiftedPerron_power_cancellation
    {y n : ℕ} (hy : 2 ≤ y) (hn : 1 ≤ n)
    (beta : ℝ) :
    (1 / (n : ℝ) ^ (1 - beta)) *
        ((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta =
      (y : ℝ) ^ (beta - 1) *
        ((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hnPos : 0 < (n : ℝ) := by positivity
  have hyratio : 0 < (y : ℝ) / n := div_pos hyPos hnPos
  have hlogy : Real.log (y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  unfold smoothSaddleHTContourRight GafniTao.sharpPerronAbscissa
  rw [Real.rpow_def_of_pos hnPos, Real.rpow_def_of_pos hyratio,
    Real.rpow_def_of_pos hyPos, Real.rpow_def_of_pos hyratio,
    Real.log_div hyPos.ne' hnPos.ne']
  rw [one_div, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem norm_smoothSaddleHTShiftedPerron_cutoffError_le_of_lt
    {y n : ℕ} {beta t T : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta) (hT : 0 < T)
    (hn : 1 ≤ n) (hny : n < y) :
    ‖smoothSaddleHTShiftedMangoldtCoefficient
          (smoothSaddleHTSourceExponent beta t) n *
        (GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) n -
          GafniTao.sharpPerronCutoff (y : ℝ) n)‖ ≤
      (y : ℝ) ^ (beta - 1) *
        (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T * Real.log ((y : ℝ) / n)))) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hnPos : 0 < (n : ℝ) := by positivity
  have hnyReal : (n : ℝ) < y := by exact_mod_cast hny
  have hright : 0 < smoothSaddleHTContourRight y beta :=
    lt_trans hbeta (smoothSaddleHTContourRight_gt hy beta)
  have hcut : GafniTao.sharpPerronCutoff (y : ℝ) n = 1 := by
    simp [GafniTao.sharpPerronCutoff, hnyReal.le]
  have hk := GafniTao.norm_sharpPerronKernel_sub_one_le_of_natCast_lt
    hright hT hyPos hn hnyReal
  rw [norm_mul,
    norm_smoothSaddleHTShiftedMangoldtCoefficient_sourceExponent hn beta t,
    hcut]
  calc
    (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta)) *
        ‖GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) n - 1‖ ≤
      (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta)) *
        (((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta /
          (Real.pi * T * Real.log ((y : ℝ) / n))) := by
        exact mul_le_mul_of_nonneg_left hk
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg hnPos.le _))
    _ = (y : ℝ) ^ (beta - 1) *
        (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T * Real.log ((y : ℝ) / n)))) := by
      calc
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta)) *
            (((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta /
              (Real.pi * T * Real.log ((y : ℝ) / n))) =
          ArithmeticFunction.vonMangoldt n *
              ((1 / (n : ℝ) ^ (1 - beta)) *
                ((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta) /
            (Real.pi * T * Real.log ((y : ℝ) / n)) := by ring
        _ = ArithmeticFunction.vonMangoldt n *
              ((y : ℝ) ^ (beta - 1) *
                ((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
            (Real.pi * T * Real.log ((y : ℝ) / n)) := by
              rw [smoothSaddleHTShiftedPerron_power_cancellation hy hn beta]
        _ = (y : ℝ) ^ (beta - 1) *
            (ArithmeticFunction.vonMangoldt n *
              (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
                (Real.pi * T * Real.log ((y : ℝ) / n)))) := by ring

theorem norm_smoothSaddleHTShiftedPerron_cutoffError_le_of_gt
    {y n : ℕ} {beta t T : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta) (hT : 0 < T)
    (hn : 1 ≤ n) (hyn : y < n) :
    ‖smoothSaddleHTShiftedMangoldtCoefficient
          (smoothSaddleHTSourceExponent beta t) n *
        (GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) n -
          GafniTao.sharpPerronCutoff (y : ℝ) n)‖ ≤
      (y : ℝ) ^ (beta - 1) *
        (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T * (-Real.log ((y : ℝ) / n))))) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hnPos : 0 < (n : ℝ) := by positivity
  have hynReal : (y : ℝ) < n := by exact_mod_cast hyn
  have hright : 0 < smoothSaddleHTContourRight y beta :=
    lt_trans hbeta (smoothSaddleHTContourRight_gt hy beta)
  have hcut : GafniTao.sharpPerronCutoff (y : ℝ) n = 0 := by
    simp [GafniTao.sharpPerronCutoff, not_le_of_gt hynReal]
  have hk := GafniTao.norm_sharpPerronKernel_le_of_natCast_lt
    hright hT hyPos hn hynReal
  rw [norm_mul,
    norm_smoothSaddleHTShiftedMangoldtCoefficient_sourceExponent hn beta t,
    hcut, sub_zero]
  calc
    (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta)) *
        ‖GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) n‖ ≤
      (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta)) *
        (((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta /
          (Real.pi * T * (-Real.log ((y : ℝ) / n)))) := by
        exact mul_le_mul_of_nonneg_left hk
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg hnPos.le _))
    _ = (y : ℝ) ^ (beta - 1) *
        (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T * (-Real.log ((y : ℝ) / n))))) := by
      calc
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 - beta)) *
            (((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta /
              (Real.pi * T * (-Real.log ((y : ℝ) / n)))) =
          ArithmeticFunction.vonMangoldt n *
              ((1 / (n : ℝ) ^ (1 - beta)) *
                ((y : ℝ) / n) ^ smoothSaddleHTContourRight y beta) /
            (Real.pi * T * (-Real.log ((y : ℝ) / n))) := by ring
        _ = ArithmeticFunction.vonMangoldt n *
              ((y : ℝ) ^ (beta - 1) *
                ((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
            (Real.pi * T * (-Real.log ((y : ℝ) / n))) := by
              rw [smoothSaddleHTShiftedPerron_power_cancellation hy hn beta]
        _ = (y : ℝ) ^ (beta - 1) *
            (ArithmeticFunction.vonMangoldt n *
              (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
                (Real.pi * T * (-Real.log ((y : ℝ) / n))))) := by ring

theorem norm_smoothSaddleHTShiftedPerron_cutoffError_le_at
    {y : ℕ} {beta t T : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta) :
    ‖smoothSaddleHTShiftedMangoldtCoefficient
          (smoothSaddleHTSourceExponent beta t) y *
        (GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) y -
          GafniTao.sharpPerronCutoff (y : ℝ) y)‖ ≤
      (y : ℝ) ^ (beta - 1) *
        (ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ)) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyOne : 1 ≤ y := by omega
  have hright : 0 < smoothSaddleHTContourRight y beta :=
    lt_trans hbeta (smoothSaddleHTContourRight_gt hy beta)
  have hcut : GafniTao.sharpPerronCutoff (y : ℝ) y = 1 := by
    simp [GafniTao.sharpPerronCutoff]
  have hkNorm := GafniTao.norm_sharpPerronKernel_at_natCast_le_half
    (T := T) hright hyPos hyOne rfl
  have hk : ‖GafniTao.sharpPerronKernel
      (smoothSaddleHTContourRight y beta) T (y : ℝ) y -
        GafniTao.sharpPerronCutoff (y : ℝ) y‖ ≤ (3 / 2 : ℝ) := by
    rw [hcut]
    calc
      ‖GafniTao.sharpPerronKernel
          (smoothSaddleHTContourRight y beta) T (y : ℝ) y - 1‖ ≤
        ‖GafniTao.sharpPerronKernel
          (smoothSaddleHTContourRight y beta) T (y : ℝ) y‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
      _ ≤ (1 / 2 : ℝ) + 1 := by simpa using add_le_add_right hkNorm 1
      _ = 3 / 2 := by norm_num
  rw [norm_mul,
    norm_smoothSaddleHTShiftedMangoldtCoefficient_sourceExponent hyOne beta t]
  calc
    (ArithmeticFunction.vonMangoldt y / (y : ℝ) ^ (1 - beta)) *
        ‖GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) y -
          GafniTao.sharpPerronCutoff (y : ℝ) y‖ ≤
      (ArithmeticFunction.vonMangoldt y / (y : ℝ) ^ (1 - beta)) *
        (3 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hk
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.rpow_nonneg hyPos.le _))
    _ = (y : ℝ) ^ (beta - 1) *
        (ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ)) := by
      have hpow : 1 / (y : ℝ) ^ (1 - beta) =
          (y : ℝ) ^ (beta - 1) := by
        rw [show beta - 1 = -(1 - beta) by ring,
          Real.rpow_neg hyPos.le]
        rw [one_div]
      rw [show ArithmeticFunction.vonMangoldt y /
          (y : ℝ) ^ (1 - beta) =
        ArithmeticFunction.vonMangoldt y *
          (1 / (y : ℝ) ^ (1 - beta)) by ring, hpow]
      ring

noncomputable def smoothSaddleHTPerronTruncationMajorant
    (y : ℕ) (T : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else if n < y then
    ArithmeticFunction.vonMangoldt n *
      (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
        (Real.pi * T * Real.log ((y : ℝ) / n)))
  else if n = y then
    ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ)
  else
    ArithmeticFunction.vonMangoldt n *
      (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
        (Real.pi * T * (-Real.log ((y : ℝ) / n))))

theorem smoothSaddleHTPerronTruncationMajorant_nonneg
    {y : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T) (n : ℕ) :
    0 ≤ smoothSaddleHTPerronTruncationMajorant y T n := by
  unfold smoothSaddleHTPerronTruncationMajorant
  split_ifs with hn0 hny hnyEq
  · exact le_rfl
  · have hnPos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hratio : 1 < (y : ℝ) / n := by
      rw [one_lt_div hnPos]
      exact_mod_cast hny
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg (Real.rpow_nonneg (div_pos (by positivity) hnPos).le _)
        (mul_nonneg (mul_nonneg Real.pi_pos.le hT.le)
          (Real.log_pos hratio).le))
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by norm_num)
  · have hyn : y < n := by omega
    have hnPos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hratioPos : 0 < (y : ℝ) / n := div_pos (by positivity) hnPos
    have hratio : (y : ℝ) / n < 1 := by
      rw [div_lt_one hnPos]
      exact_mod_cast hyn
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg (Real.rpow_nonneg hratioPos.le _)
        (mul_nonneg (mul_nonneg Real.pi_pos.le hT.le)
          (neg_nonneg.mpr (Real.log_nonpos hratioPos.le hratio.le))))

theorem norm_smoothSaddleHTShiftedPerron_cutoffError_le_majorant
    {y n : ℕ} {beta t T : ℝ}
    (hy : 2 ≤ y) (hbeta : 0 < beta) (hT : 0 < T) :
    ‖smoothSaddleHTShiftedMangoldtCoefficient
          (smoothSaddleHTSourceExponent beta t) n *
        (GafniTao.sharpPerronKernel
            (smoothSaddleHTContourRight y beta) T (y : ℝ) n -
          GafniTao.sharpPerronCutoff (y : ℝ) n)‖ ≤
      (y : ℝ) ^ (beta - 1) *
        smoothSaddleHTPerronTruncationMajorant y T n := by
  by_cases hn0 : n = 0
  · subst n
    simp [smoothSaddleHTShiftedMangoldtCoefficient, LSeries.term_def,
      smoothSaddleHTPerronTruncationMajorant]
  by_cases hny : n < y
  · simpa [smoothSaddleHTPerronTruncationMajorant, hn0, hny] using
      norm_smoothSaddleHTShiftedPerron_cutoffError_le_of_lt
        hy hbeta hT (Nat.one_le_iff_ne_zero.mpr hn0) hny
  by_cases hEq : n = y
  · subst n
    simpa [smoothSaddleHTPerronTruncationMajorant,
      Nat.ne_of_gt (by omega : 0 < y)] using
      norm_smoothSaddleHTShiftedPerron_cutoffError_le_at
        (T := T) (t := t) hy hbeta
  · have hyn : y < n := by omega
    simpa [smoothSaddleHTPerronTruncationMajorant, hn0, hny, hEq] using
      norm_smoothSaddleHTShiftedPerron_cutoffError_le_of_gt
        hy hbeta hT (Nat.one_le_iff_ne_zero.mpr hn0) hyn

theorem summable_smoothSaddleHTPerronTruncationMajorant
    {y : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T) :
    Summable (smoothSaddleHTPerronTruncationMajorant y T) := by
  let c := GafniTao.sharpPerronAbscissa (y : ℝ)
  let C := (y : ℝ) ^ c / (Real.pi * T * Real.log 2)
  let d : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  have hc : 1 < c := GafniTao.one_lt_sharpPerronAbscissa
    (by exact_mod_cast (show 1 < y by omega))
  have hd : Summable d := GafniTao.summable_vonMangoldt_div_nat_rpow hc
  have hdom : Summable (fun n => C * d n) := hd.mul_left C
  apply Summable.of_norm_bounded_eventually hdom
  rw [show (cofinite : Filter ℕ) = atTop from ?_]
  · filter_upwards [eventually_ge_atTop (2 * y)] with n hn
    have hn0 : n ≠ 0 := by omega
    have hyn : y < n := by omega
    have hny : ¬n < y := by omega
    have hEq : n ≠ y := by omega
    have hyPos : 0 < (y : ℝ) := by positivity
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hratioPos : 0 < (y : ℝ) / n := div_pos hyPos hnPos
    have hratioLe : (y : ℝ) / n ≤ 1 / 2 := by
      rw [div_le_iff₀ hnPos]
      have hnReal : 2 * (y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : Real.log 2 ≤ -Real.log ((y : ℝ) / n) := by
      have hm := Real.log_le_log hratioPos hratioLe
      have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hhalf] at hm
      linarith
    have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
    have hden : Real.pi * T * Real.log 2 ≤
        Real.pi * T * (-Real.log ((y : ℝ) / n)) :=
      mul_le_mul_of_nonneg_left hlog hpiT.le
    have hpow0 : 0 ≤ ((y : ℝ) / n) ^ c := Real.rpow_nonneg hratioPos.le _
    have hfrac :
        ((y : ℝ) / n) ^ c /
            (Real.pi * T * (-Real.log ((y : ℝ) / n))) ≤
          ((y : ℝ) / n) ^ c / (Real.pi * T * Real.log 2) :=
      div_le_div_of_nonneg_left hpow0
        (mul_pos hpiT hlogTwo) hden
    rw [Real.norm_eq_abs, abs_of_nonneg
      (smoothSaddleHTPerronTruncationMajorant_nonneg hy hT n)]
    unfold smoothSaddleHTPerronTruncationMajorant
    rw [if_neg hn0, if_neg hny, if_neg hEq]
    calc
      ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ c /
            (Real.pi * T * (-Real.log ((y : ℝ) / n)))) ≤
        ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ c / (Real.pi * T * Real.log 2)) :=
        mul_le_mul_of_nonneg_left hfrac ArithmeticFunction.vonMangoldt_nonneg
      _ = C * d n := by
        dsimp [C, d, c]
        rw [Real.div_rpow hyPos.le hnPos.le]
        ring
  · exact Nat.cofinite_eq_atTop

theorem norm_smoothSaddleHTContourTruncationError_le_tsum_majorant
    {y : ℕ} {beta ε t : ℝ} (hy : 2 ≤ y) (hbeta : 0 < beta) :
    ‖smoothSaddleHTContourTruncationError y beta ε t‖ ≤
      (y : ℝ) ^ (beta - 1) *
        ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y
          (smoothSaddleHTContourHeight y ε) n := by
  let c := smoothSaddleHTContourRight y beta
  let T := smoothSaddleHTContourHeight y ε
  let s := smoothSaddleHTSourceExponent beta t
  let f : ℕ → ℂ := fun n =>
    smoothSaddleHTShiftedMangoldtCoefficient s n *
      (GafniTao.sharpPerronKernel c T (y : ℝ) n -
        GafniTao.sharpPerronCutoff (y : ℝ) n)
  have hcBeta : beta < c := by
    exact smoothSaddleHTContourRight_gt hy beta
  have hc : 0 < c := hbeta.trans hcBeta
  have hT : 0 < T := smoothSaddleHTContourHeight_pos y ε
  have hyPos : 0 < (y : ℝ) := by positivity
  have hsPhysical : 1 < s.re + c := by
    dsimp [s, c]
    simp
    linarith
  have hk := summable_smoothSaddleHTShiftedPerronKernel
    (c := c) (T := T) (y := (y : ℝ)) (s := s) hsPhysical hc hyPos
  have hcut := summable_smoothSaddleHTShiftedPerronCutoff y s
  have hf : Summable f := by
    have hsub := hk.sub hcut
    apply hsub.congr
    intro n
    exact smoothSaddleHTShiftedPerronKernel_sub_cutoff_factor
      c T y s n
  have hmajorant := summable_smoothSaddleHTPerronTruncationMajorant hy hT
  have hscaled : Summable
      (fun n => (y : ℝ) ^ (beta - 1) *
        smoothSaddleHTPerronTruncationMajorant y T n) :=
    hmajorant.mul_left ((y : ℝ) ^ (beta - 1))
  have hpoint : ∀ n, ‖f n‖ ≤
      (y : ℝ) ^ (beta - 1) *
        smoothSaddleHTPerronTruncationMajorant y T n := by
    intro n
    exact norm_smoothSaddleHTShiftedPerron_cutoffError_le_majorant
      (n := n) (t := t) hy hbeta hT
  unfold smoothSaddleHTContourTruncationError
  change ‖∑' n : ℕ, f n‖ ≤ _
  calc
    ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ, (y : ℝ) ^ (beta - 1) *
        smoothSaddleHTPerronTruncationMajorant y T n :=
      Summable.tsum_mono hf.norm hscaled hpoint
    _ = (y : ℝ) ^ (beta - 1) *
        ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n := by
      rw [tsum_mul_left]

end

end Tao2026
