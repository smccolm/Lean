import Tao2026.SmoothNumberSaddleHTPerronTruncation
import GafniTao.SharpPerronLogDistance
import GafniTao.SharpPerronLSeries

/-!
# Arithmetic summation of the HT sharp-Perron majorant

At the integral cutoff `y`, every nonendpoint integer is at additive
distance at least one.  The logarithmic Perron denominator is therefore
bounded very coarsely by `y + 1`.  This gives a first completely explicit
arithmetic ledger.  A later sharp summation retains the reciprocal-distance
harmonic factor needed for uniform absorption over the full epsilon range.

The nonendpoint terms are then dominated by one constant multiple of the
positive von Mangoldt Dirichlet series on the optimized Perron line.  The
single endpoint is retained explicitly.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTPerronEndpointWeight
    (y n : ℕ) : ℝ :=
  if n = y then ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) else 0

theorem smoothSaddleHTPerronEndpointWeight_nonneg (y n : ℕ) :
    0 ≤ smoothSaddleHTPerronEndpointWeight y n := by
  unfold smoothSaddleHTPerronEndpointWeight
  split_ifs
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by norm_num)
  · exact le_rfl

theorem summable_smoothSaddleHTPerronEndpointWeight (y : ℕ) :
    Summable (smoothSaddleHTPerronEndpointWeight y) := by
  apply summable_of_ne_finset_zero (s := {y})
  intro n hn
  have hne : n ≠ y := by simpa using hn
  simp [smoothSaddleHTPerronEndpointWeight, hne]

theorem tsum_smoothSaddleHTPerronEndpointWeight (y : ℕ) :
    ∑' n : ℕ, smoothSaddleHTPerronEndpointWeight y n =
      ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) := by
  rw [tsum_eq_sum (s := {y})]
  · simp [smoothSaddleHTPerronEndpointWeight]
  · intro n hn
    have hne : n ≠ y := by simpa using hn
    simp [smoothSaddleHTPerronEndpointWeight, hne]

theorem one_div_log_nat_ratio_le_succ
    {y n : ℕ} (hy : 2 ≤ y) (hn : 1 ≤ n) (hny : n < y) :
    1 / Real.log ((y : ℝ) / n) ≤ (y : ℝ) + 1 := by
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnyReal : (n : ℝ) < y := by exact_mod_cast hny
  have hadd := GafniTao.one_div_log_div_le_div_sub_of_pos_of_lt hnPos hnyReal
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hdist : (1 : ℝ) ≤ (y : ℝ) - n := by
    have hdistNat : 1 ≤ y - n := by omega
    rw [← Nat.cast_sub (Nat.le_of_lt hny)]
    exact_mod_cast hdistNat
  have hdistPos : 0 < (y : ℝ) - n := zero_lt_one.trans_le hdist
  calc
    1 / Real.log ((y : ℝ) / n) ≤
        (y : ℝ) / ((y : ℝ) - n) := hadd
    _ ≤ (y : ℝ) / 1 :=
      div_le_div_of_nonneg_left hy0 zero_lt_one hdist
    _ ≤ (y : ℝ) + 1 := by linarith

theorem one_div_neg_log_nat_ratio_le_succ
    {y n : ℕ} (hy : 2 ≤ y) (hyn : y < n) :
    1 / (-Real.log ((y : ℝ) / n)) ≤ (y : ℝ) + 1 := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hynReal : (y : ℝ) < n := by exact_mod_cast hyn
  have hadd :=
    GafniTao.one_div_neg_log_div_le_div_sub_of_pos_of_lt hyPos hynReal
  have hdist : (1 : ℝ) ≤ (n : ℝ) - y := by
    have hdistNat : 1 ≤ n - y := by omega
    rw [← Nat.cast_sub (Nat.le_of_lt hyn)]
    exact_mod_cast hdistNat
  have hdistPos : 0 < (n : ℝ) - y := zero_lt_one.trans_le hdist
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hyMul : (y : ℝ) * 1 ≤ (y : ℝ) * ((n : ℝ) - y) :=
    mul_le_mul_of_nonneg_left hdist hy0
  have hquot : (n : ℝ) / ((n : ℝ) - y) ≤ (y : ℝ) + 1 := by
    rw [div_le_iff₀ hdistPos]
    nlinarith
  exact hadd.trans hquot

/-- A single Dirichlet-series majorant controls every nonendpoint term. -/
theorem smoothSaddleHTPerronTruncationMajorant_le_endpoint_add_dirichlet
    {y : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T) (n : ℕ) :
    smoothSaddleHTPerronTruncationMajorant y T n ≤
      smoothSaddleHTPerronEndpointWeight y n +
        (((y : ℝ) + 1) *
            (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
              (Real.pi * T)) *
          (ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := by
  let c := GafniTao.sharpPerronAbscissa (y : ℝ)
  have hyPos : 0 < (y : ℝ) := by positivity
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  by_cases hn0 : n = 0
  · subst n
    have hyne : (0 : ℕ) ≠ y := by omega
    simp [smoothSaddleHTPerronTruncationMajorant,
      smoothSaddleHTPerronEndpointWeight, hyne]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  by_cases hny : n < y
  · have hInv := one_div_log_nat_ratio_le_succ hy hn hny
    have hratioPos : 0 < (y : ℝ) / n := div_pos hyPos hnPos
    have hbase : 0 ≤ ArithmeticFunction.vonMangoldt n *
        ((y : ℝ) / n) ^ c / (Real.pi * T) :=
      div_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg hratioPos.le _)) hpiT.le
    have hneq : n ≠ y := Nat.ne_of_lt hny
    unfold smoothSaddleHTPerronTruncationMajorant
      smoothSaddleHTPerronEndpointWeight
    rw [if_neg hn0, if_pos hny, if_neg hneq]
    calc
      ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ c /
            (Real.pi * T * Real.log ((y : ℝ) / n))) =
        (ArithmeticFunction.vonMangoldt n *
          ((y : ℝ) / n) ^ c / (Real.pi * T)) *
            (1 / Real.log ((y : ℝ) / n)) := by ring
      _ ≤ (ArithmeticFunction.vonMangoldt n *
          ((y : ℝ) / n) ^ c / (Real.pi * T)) * ((y : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hInv hbase
      _ = (((y : ℝ) + 1) * (y : ℝ) ^ c / (Real.pi * T)) *
          (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
        rw [Real.div_rpow hyPos.le hnPos.le]
        ring
      _ = 0 + (((y : ℝ) + 1) * (y : ℝ) ^ c / (Real.pi * T)) *
          (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by ring
  · by_cases hEq : n = y
    · subst n
      unfold smoothSaddleHTPerronTruncationMajorant
        smoothSaddleHTPerronEndpointWeight
      simp [Nat.ne_of_gt (by omega : 0 < y)]
      exact mul_nonneg
        (div_nonneg
          (mul_nonneg (by positivity : 0 ≤ (y : ℝ) + 1)
            (Real.rpow_nonneg hyPos.le _)) hpiT.le)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg hyPos.le _))
    · have hyn : y < n := by omega
      have hInv := one_div_neg_log_nat_ratio_le_succ hy hyn
      have hratioPos : 0 < (y : ℝ) / n := div_pos hyPos hnPos
      have hbase : 0 ≤ ArithmeticFunction.vonMangoldt n *
          ((y : ℝ) / n) ^ c / (Real.pi * T) :=
        div_nonneg
          (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg hratioPos.le _)) hpiT.le
      unfold smoothSaddleHTPerronTruncationMajorant
        smoothSaddleHTPerronEndpointWeight
      rw [if_neg hn0, if_neg hny, if_neg hEq, if_neg hEq]
      calc
        ArithmeticFunction.vonMangoldt n *
            (((y : ℝ) / n) ^ c /
              (Real.pi * T * (-Real.log ((y : ℝ) / n)))) =
          (ArithmeticFunction.vonMangoldt n *
            ((y : ℝ) / n) ^ c / (Real.pi * T)) *
              (1 / (-Real.log ((y : ℝ) / n))) := by ring
        _ ≤ (ArithmeticFunction.vonMangoldt n *
            ((y : ℝ) / n) ^ c / (Real.pi * T)) * ((y : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hInv hbase
        _ = (((y : ℝ) + 1) * (y : ℝ) ^ c / (Real.pi * T)) *
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
          rw [Real.div_rpow hyPos.le hnPos.le]
          ring
        _ = 0 + (((y : ℝ) + 1) * (y : ℝ) ^ c / (Real.pi * T)) *
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by ring

/-- Explicit arithmetic estimate for the complete truncation majorant. -/
theorem tsum_smoothSaddleHTPerronTruncationMajorant_le_arithmetic
    {y : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T) :
    ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
      ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
        (((y : ℝ) + 1) *
            (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
              (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := by
  let c := GafniTao.sharpPerronAbscissa (y : ℝ)
  let C := ((y : ℝ) + 1) * (y : ℝ) ^ c / (Real.pi * T)
  let d : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  have hc : 1 < c := GafniTao.one_lt_sharpPerronAbscissa
    (by exact_mod_cast (show 1 < y by omega))
  have hd : Summable d := GafniTao.summable_vonMangoldt_div_nat_rpow hc
  have he := summable_smoothSaddleHTPerronEndpointWeight y
  have hmajorant := summable_smoothSaddleHTPerronTruncationMajorant hy hT
  have hright : Summable
      (fun n => smoothSaddleHTPerronEndpointWeight y n + C * d n) :=
    he.add (hd.mul_left C)
  calc
    ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
        ∑' n : ℕ, (smoothSaddleHTPerronEndpointWeight y n + C * d n) :=
      Summable.tsum_mono hmajorant hright (fun n => by
        simpa [C, d, c] using
          smoothSaddleHTPerronTruncationMajorant_le_endpoint_add_dirichlet
            hy hT n)
    _ = (∑' n : ℕ, smoothSaddleHTPerronEndpointWeight y n) +
        C * (∑' n : ℕ, d n) := by
      rw [Summable.tsum_add he (hd.mul_left C), tsum_mul_left]
    _ = _ := by
      rw [tsum_smoothSaddleHTPerronEndpointWeight]

/-- The frozen zeta bound turns the Dirichlet-series factor into
`log y + C₀`, while the optimized line contributes exactly `e*y`. -/
theorem exists_tsum_smoothSaddleHTPerronTruncationMajorant_le_explicit :
    ∃ C₀ ≥ 0, ∀ (y : ℕ) (T : ℝ), 2 ≤ y → 0 < T →
      ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
        ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (((y : ℝ) + 1) * (Real.exp 1 * y) / (Real.pi * T)) *
            (Real.log y + C₀) := by
  obtain ⟨C₀, hC₀, hseries⟩ :=
    GafniTao.exists_tsum_vonMangoldt_optimized_le
  refine ⟨C₀, hC₀, fun y T hy hT => ?_⟩
  have harith :=
    tsum_smoothSaddleHTPerronTruncationMajorant_le_arithmetic hy hT
  have hseriesY := hseries (y : ℝ)
    (by exact_mod_cast (show 1 < y by omega))
  have hcoef : 0 ≤ ((y : ℝ) + 1) *
      (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
        (Real.pi * T) := by positivity
  calc
    ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
        ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (((y : ℝ) + 1) *
              (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
                (Real.pi * T)) *
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
              (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := harith
    _ ≤ ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (((y : ℝ) + 1) *
              (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
                (Real.pi * T)) * (Real.log y + C₀) := by
      gcongr
    _ = ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (((y : ℝ) + 1) * (Real.exp 1 * y) / (Real.pi * T)) *
            (Real.log y + C₀) := by
      rw [GafniTao.rpow_sharpPerronAbscissa
        (by exact_mod_cast (show 1 < y by omega))]

/-- Complete explicit truncation-error estimate at the height selected for
the HT contour. -/
theorem exists_norm_smoothSaddleHTContourTruncationError_le_explicit :
    ∃ C₀ ≥ 0, ∀ (y : ℕ) (beta ε t : ℝ), 2 ≤ y → 0 < beta →
      ‖smoothSaddleHTContourTruncationError y beta ε t‖ ≤
        (y : ℝ) ^ (beta - 1) *
          (ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
            (((y : ℝ) + 1) * (Real.exp 1 * y) /
                (Real.pi * smoothSaddleHTContourHeight y ε)) *
              (Real.log y + C₀)) := by
  obtain ⟨C₀, hC₀, hmajorant⟩ :=
    exists_tsum_smoothSaddleHTPerronTruncationMajorant_le_explicit
  refine ⟨C₀, hC₀, fun y beta ε t hy hbeta => ?_⟩
  have hfirst :=
    norm_smoothSaddleHTContourTruncationError_le_tsum_majorant
      (ε := ε) (t := t) hy hbeta
  have hsum := hmajorant y (smoothSaddleHTContourHeight y ε) hy
    (smoothSaddleHTContourHeight_pos y ε)
  exact hfirst.trans (mul_le_mul_of_nonneg_left hsum
    (Real.rpow_nonneg (by positivity : 0 ≤ (y : ℝ)) _))

end

end Tao2026
