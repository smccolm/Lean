import Tao2026.QuantitativePNTBridge
import GafniTao.SharpPerronLowHeight
import GafniTao.FordAsymptoticZeroFree
import GafniTao.PintzVKScale
import GafniTao.CriticalStripSymmetry

/-!
# An unconditional classical quantitative PNT

This module combines the frozen sharp explicit formula with Ford's proved
zero-free region.  A deliberately coarse quadratic zero count is sufficient:
at height `exp (a * sqrt (log x))`, the logarithmic zero-free width gives the
classical de la Vallée Poussin decay after the polynomial zero count and the
sharp-truncation error are absorbed.
-/

open Complex Finset Filter Set
open scoped BigOperators Topology

namespace Tao2026

noncomputable section

open GafniTao

/-- The reciprocal weights of the finitely many nontrivial zeros of height at
most one.  All remaining zeros have norm at least one. -/
noncomputable def quantitativePNTLowZeroConstant : ℝ :=
  ∑ rho ∈ zeroSet 0 1, (zeroMultiplicity rho : ℝ) / ‖rho‖

theorem quantitativePNTLowZeroConstant_nonneg :
    0 ≤ quantitativePNTLowZeroConstant := by
  unfold quantitativePNTLowZeroConstant
  exact Finset.sum_nonneg fun _ _ =>
    div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- The frozen global Jensen estimate, used only with epsilon one, gives a
coarse eventual quadratic bound for the complete critical-strip zero count. -/
theorem exists_eventually_zeroCount_zero_le_quadratic :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      (zeroCount 0 T : ℝ) ≤ K * T ^ (2 : ℝ) := by
  have hO := lowerHalf_zeroCount_epsilon_one (sigma := 0) (by norm_num)
    1 zero_lt_one
  obtain ⟨K₀, hK₀⟩ := hO.bound
  let K : ℝ := max K₀ 1
  refine ⟨K, by dsimp [K]; linarith [le_max_right K₀ 1], ?_⟩
  filter_upwards [hK₀, eventually_gt_atTop (0 : ℝ)] with T hT hTPos
  have hCountNonneg : 0 ≤ (zeroCount 0 T : ℝ) := by positivity
  have hRightNonneg : 0 ≤ T ^ (1 : ℝ) * |T ^ (1 : ℝ)| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hCountNonneg,
    Real.norm_eq_abs, abs_of_nonneg hRightNonneg,
    Real.rpow_one, abs_of_pos hTPos] at hT
  rw [abs_of_nonneg hCountNonneg] at hT
  calc
    (zeroCount 0 T : ℝ) ≤ K₀ * (T * T) := hT
    _ ≤ K * (T * T) := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hTPos.le hTPos.le)
    _ = K * T ^ (2 : ℝ) := by rw [Real.rpow_two, pow_two]

/-- Ford's rectangle region implies the weaker classical logarithmic strip,
which is the exact scale needed for the de la Vallée Poussin optimization. -/
theorem zero_re_le_one_sub_log_width
    {c H T : ℝ} (hc : 0 < c)
    (hzero : VinogradovKorobovRectangleZeroFree c H)
    (hbase : Real.exp (Real.exp 1) ≤ T) (hHT : H ≤ T)
    {rho : ℂ} (hrho : rho ∈ zeroSet 0 T) :
    rho.re ≤ 1 - c / Real.log T := by
  have hrect := (hzero hHT).2.2 hrho
  have hDpos := vinogradovKorobovDenominator_pos hbase
  have hDle := vinogradovKorobovDenominator_le_log hbase
  have hwidth : c / Real.log T ≤ c / vinogradovKorobovDenominator T :=
    div_le_div_of_nonneg_left hc.le hDpos hDle
  linarith

/-- A single zero term inherits the common logarithmic exponent supplied by
the rectangle zero-free region. -/
theorem norm_quantitativePNT_zero_term_le
    {c H T x : ℝ} (hc : 0 < c)
    (hzero : VinogradovKorobovRectangleZeroFree c H)
    (hbase : Real.exp (Real.exp 1) ≤ T) (hHT : H ≤ T)
    (hx : 1 ≤ x) {rho : ℂ} (hrho : rho ∈ zeroSet 0 T) :
    ‖(zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ ≤
      (zeroMultiplicity rho : ℝ) *
        (x ^ (1 - c / Real.log T) / ‖rho‖) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hre := zero_re_le_one_sub_log_width hc hzero hbase hHT hrho
  have hpow : x ^ rho.re ≤ x ^ (1 - c / Real.log T) :=
    Real.rpow_le_rpow_of_exponent_le hx hre
  rw [norm_mul, RCLike.norm_natCast, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
  gcongr

/-- The complete truncated zero sum is controlled by the common zero-free
exponent times the low-zero reciprocal mass and the multiplicity count. -/
theorem norm_truncatedPsiZeroSum_le_log_width
    {c H T x : ℝ} (hc : 0 < c)
    (hzero : VinogradovKorobovRectangleZeroFree c H)
    (hbase : Real.exp (Real.exp 1) ≤ T) (hHT : H ≤ T)
    (hx : 1 ≤ x) :
    ‖truncatedPsiZeroSum T x‖ ≤
      x ^ (1 - c / Real.log T) *
        (quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ)) := by
  let S := zeroSet 0 T
  let L := zeroSet 0 1
  let P : ℝ := x ^ (1 - c / Real.log T)
  have hP : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  have hweight :
      (∑ rho ∈ S,
          if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖
          else (zeroMultiplicity rho : ℝ)) ≤
        quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ) := by
    have hlow :
        (∑ rho ∈ S,
            if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖ else 0) ≤
          quantitativePNTLowZeroConstant := by
      have hsubset : S.filter (fun rho => rho ∈ L) ⊆ L := by
        intro rho hrho
        exact (Finset.mem_filter.mp hrho).2
      calc
        (∑ rho ∈ S,
            if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖ else 0) =
            ∑ rho ∈ S.filter (fun rho => rho ∈ L),
              (zeroMultiplicity rho : ℝ) / ‖rho‖ := by
          exact (Finset.sum_filter (fun rho => rho ∈ L)
            (fun rho => (zeroMultiplicity rho : ℝ) / ‖rho‖)).symm
        _ ≤ ∑ rho ∈ L, (zeroMultiplicity rho : ℝ) / ‖rho‖ := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun rho _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg rho))
        _ = quantitativePNTLowZeroConstant := by
          simp [quantitativePNTLowZeroConstant, L]
    calc
      (∑ rho ∈ S,
          if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖
          else (zeroMultiplicity rho : ℝ)) ≤
          ∑ rho ∈ S,
            ((if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖ else 0) +
              (zeroMultiplicity rho : ℝ)) := by
            apply Finset.sum_le_sum
            intro rho hrho
            by_cases hL : rho ∈ L <;> simp [hL, Nat.cast_nonneg]
      _ = (∑ rho ∈ S,
            if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖ else 0) +
          ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) := by
            rw [Finset.sum_add_distrib]
      _ ≤ quantitativePNTLowZeroConstant +
          ∑ rho ∈ S, (zeroMultiplicity rho : ℝ) := add_le_add hlow le_rfl
      _ = quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ) := by
        rw [zeroCount_eq_weighted_sum]
        simp [S]
  unfold truncatedPsiZeroSum
  calc
    ‖∑ rho ∈ zeroSet 0 T,
        (zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ ≤
      ∑ rho ∈ zeroSet 0 T,
        ‖(zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ S,
        P * (if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖
          else (zeroMultiplicity rho : ℝ)) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hterm := norm_quantitativePNT_zero_term_le
        hc hzero hbase hHT hx (by simpa [S] using hrho)
      by_cases hlow : rho ∈ L
      · calc
          ‖(zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ ≤
              (zeroMultiplicity rho : ℝ) * (P / ‖rho‖) := hterm
          _ = P * ((zeroMultiplicity rho : ℝ) / ‖rho‖) := by ring
          _ = P * (if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖
              else (zeroMultiplicity rho : ℝ)) := by simp [hlow]
      · have habs : 1 < |rho.im| := by
          by_contra hnot
          have hle : |rho.im| ≤ 1 := le_of_not_gt hnot
          exact hlow (by
            dsimp [L]
            exact mem_zeroSet_of_abs_im_le (by simpa [S] using hrho) hle)
        have hnorm : 1 ≤ ‖rho‖ :=
          le_trans habs.le (Complex.abs_im_le_norm rho)
        have hdiv : P / ‖rho‖ ≤ P := div_le_self hP hnorm
        calc
          ‖(zeroMultiplicity rho : ℂ) * ((x : ℂ) ^ rho / rho)‖ ≤
              (zeroMultiplicity rho : ℝ) * (P / ‖rho‖) := hterm
          _ ≤ (zeroMultiplicity rho : ℝ) * P :=
            mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
          _ = P * (if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖
              else (zeroMultiplicity rho : ℝ)) := by simp [hlow, mul_comm]
    _ = P * (∑ rho ∈ S,
        if rho ∈ L then (zeroMultiplicity rho : ℝ) / ‖rho‖
          else (zeroMultiplicity rho : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ P * (quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ)) :=
      mul_le_mul_of_nonneg_left hweight hP
    _ = x ^ (1 - c / Real.log T) *
        (quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ)) := by rfl

/-- A small positive coefficient used for the classical Perron height. -/
noncomputable def quantitativePNTScale (c : ℝ) : ℝ := min 1 (c / 8)

theorem quantitativePNTScale_pos {c : ℝ} (hc : 0 < c) :
    0 < quantitativePNTScale c := by
  unfold quantitativePNTScale
  exact lt_min zero_lt_one (div_pos hc (by norm_num))

theorem quantitativePNTScale_le_one (c : ℝ) :
    quantitativePNTScale c ≤ 1 := by
  exact min_le_left _ _

theorem quantitativePNTScale_le_eighth {c : ℝ} :
    quantitativePNTScale c ≤ c / 8 := by
  exact min_le_right _ _

/-- The exponentially growing height used in the classical contour
optimization. -/
noncomputable def quantitativePNTHeight (c x : ℝ) : ℝ :=
  Real.exp (quantitativePNTScale c * Real.sqrt (Real.log x))

theorem tendsto_quantitativePNTHeight_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (quantitativePNTHeight c) atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hmul : Tendsto
      (fun x : ℝ => quantitativePNTScale c * Real.sqrt (Real.log x))
      atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (quantitativePNTScale_pos hc)).mpr hsqrt
  exact Real.tendsto_exp_atTop.comp hmul

/-- The chosen Perron height is eventually no larger than its real endpoint. -/
theorem eventually_quantitativePNTHeight_le_self (c : ℝ) :
    ∀ᶠ x : ℝ in atTop, quantitativePNTHeight c x ≤ x := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with x hlog hxOne
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hsqrtOne : 1 ≤ Real.sqrt (Real.log x) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.log x by linarith),
      Real.sqrt_nonneg (Real.log x)]
  have hscale := quantitativePNTScale_le_one c
  have hexp : quantitativePNTScale c * Real.sqrt (Real.log x) ≤ Real.log x := by
    calc
      quantitativePNTScale c * Real.sqrt (Real.log x) ≤
          Real.sqrt (Real.log x) :=
        mul_le_of_le_one_left (Real.sqrt_nonneg _) hscale
      _ ≤ Real.sqrt (Real.log x) ^ 2 := by nlinarith
      _ = Real.log x := Real.sq_sqrt (by linarith)
  unfold quantitativePNTHeight
  calc
    Real.exp (quantitativePNTScale c * Real.sqrt (Real.log x)) ≤
        Real.exp (Real.log x) := Real.exp_le_exp.mpr hexp
    _ = x := Real.exp_log hxPos

/-- At the optimized height, the common zero-free exponent absorbs a
quadratic zero count while retaining an exponential square-root saving. -/
theorem quantitativePNT_rpow_mul_height_sq_le
    {c a x : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hxPos : 0 < x)
    (haC : a ≤ c / 8) (hlog : 1 ≤ Real.log x) :
    x ^ (1 - c / Real.log (Real.exp (a * Real.sqrt (Real.log x)))) *
        Real.exp (a * Real.sqrt (Real.log x)) ^ (2 : ℝ) ≤
      x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
  let s : ℝ := Real.sqrt (Real.log x)
  have hsPos : 0 < s := Real.sqrt_pos.2 (zero_lt_one.trans_le hlog)
  have hsSq : s ^ 2 = Real.log x := Real.sq_sqrt (by linarith)
  have haa : a ^ 2 ≤ a := by nlinarith
  have hcoef : (5 / 2 : ℝ) * a ^ 2 ≤ c := by
    have h8 : 8 * a ≤ c := by linarith
    nlinarith
  rw [Real.rpow_def_of_pos hxPos,
    Real.rpow_def_of_pos (Real.exp_pos (a * s)), Real.log_exp]
  have hrhs :
      Real.exp (Real.log x + (-(a / 2) * s)) =
        x * Real.exp (-(a / 2) * s) := by
    rw [Real.exp_add, Real.exp_log hxPos]
  rw [← Real.exp_add, ← hrhs]
  apply Real.exp_le_exp.mpr
  field_simp [ha.ne', hsPos.ne']
  nlinarith

/-- The logarithmic factor in the sharp Perron remainder is absorbed by half
of the exponential square-root decay furnished by the chosen height. -/
theorem eventually_log_sq_div_exp_sqrt_le
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x ^ 2 /
          Real.exp (a * Real.sqrt (Real.log x)) ≤
        Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hratio : ∀ᶠ x : ℝ in atTop,
      1 ≤ Real.exp ((a / 2) * Real.sqrt (Real.log x)) /
        Real.sqrt (Real.log x) ^ (4 : ℝ) :=
    ((tendsto_exp_mul_div_rpow_atTop (4 : ℝ) (a / 2) (by positivity)).comp
      hsqrt).eventually (eventually_ge_atTop 1)
  filter_upwards [hratio,
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with x hratioX hlogX
  let s : ℝ := Real.sqrt (Real.log x)
  have hsPos : 0 < s := Real.sqrt_pos.2 hlogX
  have hsSq : s ^ 2 = Real.log x := Real.sq_sqrt hlogX.le
  have hsPowPos : 0 < s ^ (4 : ℝ) := Real.rpow_pos_of_pos hsPos _
  have hpoly : s ^ 4 ≤ Real.exp ((a / 2) * s) := by
    have hraw := (le_div_iff₀ hsPowPos).mp (by simpa [s] using hratioX)
    simpa [Real.rpow_natCast] using hraw
  rw [div_le_iff₀ (Real.exp_pos (a * s))]
  calc
    Real.log x ^ 2 = s ^ 4 := by rw [← hsSq]; ring
    _ ≤ Real.exp ((a / 2) * s) := hpoly
    _ = Real.exp (-(a / 2) * s) * Real.exp (a * s) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The classical de la Vallée Poussin quantitative prime number theorem,
proved unconditionally from the frozen Ford zero-free theorem, quadratic
Jensen zero count, and sharp explicit formula. -/
theorem classicalChebyshevPsiDeLaValleePoussin_native :
    ClassicalChebyshevPsiDeLaValleePoussin := by
  obtain ⟨C₀, hC₀, hsharp⟩ := sharpPsiTruncationBound_native
  obtain ⟨c₀, H, hc₀, hHbase, hpointwise⟩ :=
    ford_asymptotic_zero_free_native
  obtain ⟨c, hc, _hcLe, hrectangle⟩ :=
    exists_vinogradovKorobovRectangleZeroFree_of_pointwise
      hc₀ hHbase hpointwise
  obtain ⟨K, hK, hcount⟩ := exists_eventually_zeroCount_zero_le_quadratic
  let a : ℝ := quantitativePNTScale c
  have ha : 0 < a := quantitativePNTScale_pos hc
  have haOne : a ≤ 1 := quantitativePNTScale_le_one c
  have haC : a ≤ c / 8 := quantitativePNTScale_le_eighth
  let B : ℝ := quantitativePNTLowZeroConstant + K
  have hB : 0 < B := by
    dsimp [B]
    linarith [quantitativePNTLowZeroConstant_nonneg]
  refine ⟨C₀ + B, a / 2, add_pos hC₀ hB, by positivity, ?_⟩
  have hheight := tendsto_quantitativePNTHeight_atTop hc
  have hcountHeight := hheight.eventually hcount
  have hheightBase := hheight.eventually
    (eventually_ge_atTop (Real.exp (Real.exp 1)))
  have hheightH := hheight.eventually (eventually_ge_atTop H)
  have hheightTwo := hheight.eventually (eventually_ge_atTop (2 : ℝ))
  have hheightLe := eventually_quantitativePNTHeight_le_self c
  have habsorb := eventually_log_sq_div_exp_sqrt_le ha
  filter_upwards [hcountHeight, hheightBase, hheightH, hheightTwo,
    hheightLe, habsorb, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hcountX hbaseX hHX htwoX hheightLeX habsorbX hxTwo hlogX
  let T : ℝ := quantitativePNTHeight c x
  have hTdef : T = Real.exp (a * Real.sqrt (Real.log x)) := by
    rfl
  have hxPos : 0 < x := by linarith
  have hTPos : 0 < T := by rw [hTdef]; positivity
  have hTOne : 1 ≤ T := by linarith
  have hzero := norm_truncatedPsiZeroSum_le_log_width
    hc hrectangle (by simpa [T] using hbaseX) (by simpa [T] using hHX)
    (by linarith : 1 ≤ x)
  have hsharpX := hsharp (by simpa [T] using htwoX)
    (by simpa [T] using hheightLeX) hxTwo
  have herror :
      ‖sharpPsiTruncationError T x‖ ≤
        C₀ * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
    calc
      ‖sharpPsiTruncationError T x‖ ≤
          C₀ * x * Real.log x ^ 2 / T := hsharpX
      _ = C₀ * x * (Real.log x ^ 2 / T) := by ring
      _ ≤ C₀ * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀.le hxPos.le)
        simpa [T, quantitativePNTHeight, a] using habsorbX
  have hzeroFinal :
      ‖truncatedPsiZeroSum T x‖ ≤
        B * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
    have hcountXT : (zeroCount 0 T : ℝ) ≤ K * T ^ (2 : ℝ) := by
      simpa [T] using hcountX
    have hlowGrow : quantitativePNTLowZeroConstant ≤
        quantitativePNTLowZeroConstant * T ^ (2 : ℝ) := by
      have hTsq : 1 ≤ T ^ (2 : ℝ) := by
        rw [Real.rpow_two, pow_two]
        nlinarith
      simpa using mul_le_mul_of_nonneg_left hTsq
        quantitativePNTLowZeroConstant_nonneg
    have hcoeff :
        quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ) ≤
          B * T ^ (2 : ℝ) := by
      calc
        quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ) ≤
            quantitativePNTLowZeroConstant * T ^ (2 : ℝ) +
              K * T ^ (2 : ℝ) := add_le_add hlowGrow hcountXT
        _ = B * T ^ (2 : ℝ) := by simp [B]; ring
    calc
      ‖truncatedPsiZeroSum T x‖ ≤
          x ^ (1 - c / Real.log T) *
            (quantitativePNTLowZeroConstant + (zeroCount 0 T : ℝ)) := hzero
      _ ≤ x ^ (1 - c / Real.log T) * (B * T ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoeff (Real.rpow_nonneg hxPos.le _)
      _ = B * (x ^ (1 - c / Real.log T) * T ^ (2 : ℝ)) := by ring
      _ ≤ B * (x * Real.exp (-(a / 2) * Real.sqrt (Real.log x))) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        simpa [hTdef] using
          (quantitativePNT_rpow_mul_height_sq_le ha haOne hxPos haC hlogX)
      _ = B * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by ring
  have hidentity :
      (((Chebyshev.psi x - x : ℝ) : ℂ)) =
        sharpPsiTruncationError T x - truncatedPsiZeroSum T x := by
    unfold sharpPsiTruncationError
    ring
  have habsNorm :
      |Chebyshev.psi x - x| = ‖(((Chebyshev.psi x - x : ℝ) : ℂ))‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habsNorm, hidentity]
  calc
    ‖sharpPsiTruncationError T x - truncatedPsiZeroSum T x‖ ≤
        ‖sharpPsiTruncationError T x‖ + ‖truncatedPsiZeroSum T x‖ :=
      norm_sub_le _ _
    _ ≤ C₀ * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) +
        B * x * Real.exp (-(a / 2) * Real.sqrt (Real.log x)) :=
      add_le_add herror hzeroFinal
    _ = (C₀ + B) * x *
        Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by ring

/-- The low-frequency Mangoldt discrepancy input is therefore unconditional. -/
theorem classicalMangoldtDiscrepancyLogSaving_native :
    ClassicalMangoldtDiscrepancyLogSaving :=
  classicalMangoldtDiscrepancyLogSaving_of_chebyshevPsiDeLaValleePoussin
    classicalChebyshevPsiDeLaValleePoussin_native

/-- After discharging the quantitative-PNT side, the specialized Theorem 2.5
endpoint has exactly one remaining analytic input: Vinogradov's polynomial
exponential-sum estimate. -/
theorem taoTheorem25Specialized_of_vinogradov
    (hVinogradov : VinogradovExponentialSumEstimate) :
    TaoTheorem25SpecializedConclusion :=
  taoTheorem25Specialized_of_analyticInputs
    classicalMangoldtDiscrepancyLogSaving_native hVinogradov

end

end Tao2026
