import RiemannZeta.GuthMaynard.HughesYoungEquation96Derivatives
import RiemannZeta.GuthMaynard.HughesYoungAbsoluteConvergence

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Absolute convergence after the two DFI logarithmic operators

Hughes--Young move the equation-(84) contour to `Re s = 1` before
rearranging the complete shift and modulus sums.  At that line the
arithmetic term is equation (96) with `(a,b,c) = (1,1,2)`.  The two
logarithmic factors in DFI equation (27) are the two parameter operators
recorded in `HughesYoungEquation96Derivatives`.

This file proves the quantitative absolute convergence needed to apply
those operators to the complete series.  The logarithms are absorbed into
an arbitrarily small loss in the two positive coordinates; no dyadic box is
estimated separately.
-/

noncomputable def hughesYoungEquation96PositiveLogA
    (h : ℕ) (l : ℕ+) : ℂ :=
  Complex.log (Nat.gcd h (l : ℕ) : ℂ) - Complex.log ((l : ℕ) : ℂ)

noncomputable def hughesYoungEquation96PositiveLogB
    (k : ℕ) (l : ℕ+) : ℂ :=
  Complex.log (Nat.gcd k (l : ℕ) : ℂ) - Complex.log ((l : ℕ) : ℂ)

noncomputable def hughesYoungEquation96PositiveLogR (r : ℕ+) : ℂ :=
  Complex.log ((r : ℕ) : ℂ)

noncomputable def hughesYoungDFIPositiveLogFactorLeft
    (h : ℕ) (y : ℕ+ × ℕ+) : ℂ :=
  hughesYoungEquation96PositiveLogR y.2 +
    2 * Real.eulerMascheroniConstant +
    2 * hughesYoungEquation96PositiveLogA h y.1 - Complex.log (h : ℂ)

noncomputable def hughesYoungDFIPositiveLogFactorRight
    (k : ℕ) (y : ℕ+ × ℕ+) : ℂ :=
  hughesYoungEquation96PositiveLogR y.2 +
    2 * Real.eulerMascheroniConstant +
    2 * hughesYoungEquation96PositiveLogB k y.1 - Complex.log (k : ℂ)

/-- Multiplying the common-divisor majorant by powers of its two physical
coordinates is exactly a loss in the two convergence exponents. -/
theorem mul_rpow_commonDivisorMajorant_eq
    (A C η : ℝ) (y : ℕ+ × ℕ+) :
    ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η *
        hughesYoungCommonDivisorMajorant A C y =
      hughesYoungCommonDivisorMajorant (A - η) (C - η) y := by
  have hl : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
  have hr : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
  unfold hughesYoungCommonDivisorMajorant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [show (((y.1 : ℕ) : ℝ) ^ A) =
      (((y.1 : ℕ) : ℝ) ^ η) * (((y.1 : ℕ) : ℝ) ^ (A - η)) by
        rw [← Real.rpow_add hl]
        congr 1
        ring]
  rw [show (((y.2 : ℕ) : ℝ) ^ (1 + C)) =
      (((y.2 : ℕ) : ℝ) ^ η) *
        (((y.2 : ℕ) : ℝ) ^ (1 + (C - η))) by
        rw [← Real.rpow_add hr]
        congr 1
        ring]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hl η),
    ne_of_gt (Real.rpow_pos_of_pos hr η),
    ne_of_gt (Real.rpow_pos_of_pos hl (A - η)),
    ne_of_gt (Real.rpow_pos_of_pos hr (1 + (C - η)))]

/-- The logarithmic difference contributed by either gcd exponent is at
most twice the logarithm of the positive modulus coordinate. -/
theorem norm_hughesYoungEquation96PositiveLogA_le
    (h : ℕ) (l : ℕ+) :
    ‖hughesYoungEquation96PositiveLogA h l‖ ≤
      2 * Real.log ((l : ℕ) : ℝ) := by
  have hg : 0 < Nat.gcd h (l : ℕ) :=
    Nat.gcd_pos_of_pos_right h l.2
  have hgl : Nat.gcd h (l : ℕ) ≤ (l : ℕ) := Nat.gcd_le_right h l.2
  have hlogg : 0 ≤ Real.log (Nat.gcd h (l : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hg)
  have hlogl : 0 ≤ Real.log ((l : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast l.2)
  have hmono : Real.log (Nat.gcd h (l : ℕ) : ℝ) ≤
      Real.log ((l : ℕ) : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (Nat.gcd h (l : ℕ) : ℝ) ∈ Set.Ioi 0 by
        simpa only [Set.mem_Ioi] using (show (0 : ℝ) < Nat.gcd h (l : ℕ) by
          exact_mod_cast hg))
      (show ((l : ℕ) : ℝ) ∈ Set.Ioi 0 by
        simpa only [Set.mem_Ioi] using (show (0 : ℝ) < (l : ℕ) by
          exact_mod_cast l.2))
      (by exact_mod_cast hgl)
  unfold hughesYoungEquation96PositiveLogA
  rw [← Complex.natCast_log, ← Complex.natCast_log]
  calc
    ‖(Real.log (Nat.gcd h (l : ℕ) : ℝ) : ℂ) -
        (Real.log ((l : ℕ) : ℝ) : ℂ)‖ ≤
      ‖(Real.log (Nat.gcd h (l : ℕ) : ℝ) : ℂ)‖ +
        ‖(Real.log ((l : ℕ) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ = Real.log (Nat.gcd h (l : ℕ) : ℝ) +
        Real.log ((l : ℕ) : ℝ) := by
      rw [Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hlogg, abs_of_nonneg hlogl]
    _ ≤ 2 * Real.log ((l : ℕ) : ℝ) := by linarith

theorem norm_hughesYoungEquation96PositiveLogB_le
    (k : ℕ) (l : ℕ+) :
    ‖hughesYoungEquation96PositiveLogB k l‖ ≤
      2 * Real.log ((l : ℕ) : ℝ) := by
  simpa only [hughesYoungEquation96PositiveLogB,
    hughesYoungEquation96PositiveLogA] using
      norm_hughesYoungEquation96PositiveLogA_le k l

/-- Each DFI logarithmic factor costs at most one small power of each
positive coordinate. -/
theorem norm_hughesYoungDFIPositiveLogFactorLeft_le
    {η : ℝ} (hη : 0 < η) {h : ℕ} (hh : 0 < h) (y : ℕ+ × ℕ+) :
    ‖hughesYoungDFIPositiveLogFactorLeft h y‖ ≤
      (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) * (h : ℝ) ^ η *
        ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl1 : (1 : ℝ) ≤ (y.1 : ℕ) := by exact_mod_cast y.1.2
  have hr1 : (1 : ℝ) ≤ (y.2 : ℕ) := by exact_mod_cast y.2.2
  have hlp : 1 ≤ (((y.1 : ℕ) : ℝ) ^ η) := Real.one_le_rpow hl1 hη.le
  have hrp : 1 ≤ (((y.2 : ℕ) : ℝ) ^ η) := Real.one_le_rpow hr1 hη.le
  have hlogl := Real.log_natCast_le_rpow_div (y.1 : ℕ) hη
  have hlogr := Real.log_natCast_le_rpow_div (y.2 : ℕ) hη
  have hlogh := Real.log_natCast_le_rpow_div h hη
  have hηinv : 0 < η⁻¹ := inv_pos.mpr hη
  have hhp : 1 ≤ (h : ℝ) ^ η := Real.one_le_rpow hh1 hη.le
  have hprodRaw : (1 : ℝ) * 1 ≤
      (((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η) :=
    mul_le_mul hlp hrp (by norm_num) (by linarith [hlp])
  have hprod1 : 1 ≤ (((y.1 : ℕ) : ℝ) ^ η * (((y.2 : ℕ) : ℝ) ^ η)) := by
    simpa only [one_mul] using hprodRaw
  unfold hughesYoungDFIPositiveLogFactorLeft
  calc
    ‖(hughesYoungEquation96PositiveLogR y.2 +
        2 * (Real.eulerMascheroniConstant : ℂ) +
        2 * hughesYoungEquation96PositiveLogA h y.1) -
        Complex.log (h : ℂ)‖ ≤
      ‖hughesYoungEquation96PositiveLogR y.2‖ +
        ‖2 * (Real.eulerMascheroniConstant : ℂ)‖ +
        ‖2 * hughesYoungEquation96PositiveLogA h y.1‖ +
        ‖Complex.log (h : ℂ)‖ := by
      calc
        _ ≤ ‖hughesYoungEquation96PositiveLogR y.2 +
            2 * (Real.eulerMascheroniConstant : ℂ) +
            2 * hughesYoungEquation96PositiveLogA h y.1‖ +
            ‖Complex.log (h : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact
            (norm_add_le
          (hughesYoungEquation96PositiveLogR y.2 +
            2 * (Real.eulerMascheroniConstant : ℂ))
          (2 * hughesYoungEquation96PositiveLogA h y.1)).trans
              (by
                gcongr
                exact norm_add_le (hughesYoungEquation96PositiveLogR y.2)
                  (2 * (Real.eulerMascheroniConstant : ℂ)))
    _ ≤ Real.log ((y.2 : ℕ) : ℝ) +
        2 * |Real.eulerMascheroniConstant| +
        4 * Real.log ((y.1 : ℕ) : ℝ) + Real.log (h : ℝ) := by
      have hlogrNorm : ‖hughesYoungEquation96PositiveLogR y.2‖ =
          Real.log ((y.2 : ℕ) : ℝ) := by
        unfold hughesYoungEquation96PositiveLogR
        rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (Real.log_nonneg hr1)
      have hgammaNorm : ‖(2 : ℂ) * (Real.eulerMascheroniConstant : ℂ)‖ =
          2 * |Real.eulerMascheroniConstant| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      have hlogANorm : ‖(2 : ℂ) * hughesYoungEquation96PositiveLogA h y.1‖ ≤
          4 * Real.log ((y.1 : ℕ) : ℝ) := by
        rw [norm_mul]
        norm_num
        linarith [norm_hughesYoungEquation96PositiveLogA_le h y.1]
      have hloghNorm : ‖Complex.log (h : ℂ)‖ = Real.log (h : ℝ) := by
        rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg hh1)]
      rw [hlogrNorm, hgammaNorm, hloghNorm]
      have hlogr0 : 0 ≤ Real.log ((y.2 : ℕ) : ℝ) := Real.log_nonneg hr1
      linarith
    _ ≤ (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) * (h : ℝ) ^ η *
        ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η := by
      have hl0 : 0 ≤ (((y.1 : ℕ) : ℝ) ^ η) := by positivity
      have hr0 : 0 ≤ (((y.2 : ℕ) : ℝ) ^ η) := by positivity
      have hL : Real.log ((y.1 : ℕ) : ℝ) ≤
          η⁻¹ * (((y.1 : ℕ) : ℝ) ^ η) := by
        simpa [div_eq_mul_inv, mul_comm] using hlogl
      have hR : Real.log ((y.2 : ℕ) : ℝ) ≤
          η⁻¹ * (((y.2 : ℕ) : ℝ) ^ η) := by
        simpa [div_eq_mul_inv, mul_comm] using hlogr
      have hH : Real.log (h : ℝ) ≤ η⁻¹ * (h : ℝ) ^ η := by
        simpa [div_eq_mul_inv, mul_comm] using hlogh
      have hfull1 : 1 ≤ (h : ℝ) ^ η *
          ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η)) := by
        nlinarith [mul_le_mul hhp hprod1 (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith [hhp] : (0 : ℝ) ≤ (h : ℝ) ^ η)]
      have hbase_le_full :
          (((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η) ≤
            (h : ℝ) ^ η *
              ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η)) := by
        exact le_mul_of_one_le_left
          (mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (Real.rpow_nonneg (by positivity) _)) hhp
      have hLp : η⁻¹ * (((y.1 : ℕ) : ℝ) ^ η) ≤
          η⁻¹ * ((h : ℝ) ^ η *
            ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η))) := by
        apply mul_le_mul_of_nonneg_left _ hηinv.le
        exact (le_mul_of_one_le_right hl0 hrp).trans hbase_le_full
      have hRp : η⁻¹ * (((y.2 : ℕ) : ℝ) ^ η) ≤
          η⁻¹ * ((h : ℝ) ^ η *
            ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η))) := by
        apply mul_le_mul_of_nonneg_left _ hηinv.le
        exact (le_mul_of_one_le_left hr0 hlp).trans hbase_le_full
      have hHp : η⁻¹ * (h : ℝ) ^ η ≤
          η⁻¹ * ((h : ℝ) ^ η *
            ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η))) := by
        exact mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _) hprod1)
          hηinv.le
      have hGamma : 2 * |Real.eulerMascheroniConstant| ≤
          2 * |Real.eulerMascheroniConstant| *
            ((h : ℝ) ^ η *
              ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η))) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfull1
            (show 0 ≤ 2 * |Real.eulerMascheroniConstant| by positivity))
      calc
        _ ≤ (η⁻¹ + 4 * η⁻¹ + η⁻¹ +
            2 * |Real.eulerMascheroniConstant|) *
              ((h : ℝ) ^ η *
                ((((y.1 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η))) := by
          linarith
        _ = _ := by ring

theorem norm_hughesYoungDFIPositiveLogFactorRight_le
    {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : 0 < k) (y : ℕ+ × ℕ+) :
    ‖hughesYoungDFIPositiveLogFactorRight k y‖ ≤
      (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) * (k : ℝ) ^ η *
        ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η := by
  simpa only [hughesYoungDFIPositiveLogFactorRight,
    hughesYoungDFIPositiveLogFactorLeft,
    hughesYoungEquation96PositiveLogB,
    hughesYoungEquation96PositiveLogA] using
      norm_hughesYoungDFIPositiveLogFactorLeft_le hη hk y

/-- Absolute convergence of the equation-(96) series after applying both
DFI logarithmic operators at the source line `Re s = 1`. -/
theorem summable_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1 2 y *
        hughesYoungDFIPositiveLogFactorLeft h y *
        hughesYoungDFIPositiveLogFactorRight k y) := by
  let θ : ℝ := 1 / 2 + 2 * η
  let A : ℝ := 1 + 2 * η
  let C : ℝ := 1 - 2 * η
  let B : ℝ := 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|
  let K : ℝ := ((h : ℝ) ^ θ * (k : ℝ) ^ θ) * B ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hθ : 1 / 2 < θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hA : 1 < A := by dsimp [A]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hK : 0 ≤ K := by dsimp [K, B]; positivity
  have hmajor : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant A C y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  apply Summable.of_norm_bounded hmajor
  intro y
  have hterm := norm_hughesYoungEquation96PositiveTerm_one_one_le
    hh hk (show 0 ≤ θ by linarith [hθ]) hθ1 (1 : ℂ) y
  have hterm' :
      ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ ≤
        ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y := by
    convert hterm using 1
    all_goals norm_num
  have hleft := norm_hughesYoungDFIPositiveLogFactorLeft_le hη hh y
  have hright := norm_hughesYoungDFIPositiveLogFactorRight_le hη hk y
  have hcommon0 : 0 ≤ hughesYoungCommonDivisorMajorant (2 * θ) 1 y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hpow0 : 0 ≤ (((y.1 : ℕ) : ℝ) ^ η * (((y.2 : ℕ) : ℝ) ^ η)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  rw [norm_mul, norm_mul]
  calc
    ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ *
        ‖hughesYoungDFIPositiveLogFactorLeft h y‖ *
        ‖hughesYoungDFIPositiveLogFactorRight k y‖ ≤
      (((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y) *
        (B * (h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) *
        (B * (k : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) := by
      gcongr
    _ = K *
        (((((y.1 : ℕ) : ℝ) ^ (2 * η)) *
            (((y.2 : ℕ) : ℝ) ^ (2 * η))) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y) := by
      have hl : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
      have hr : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
      rw [show (((y.1 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.1 : ℕ) : ℝ) ^ η) * (((y.1 : ℕ) : ℝ) ^ η) by
            rw [← Real.rpow_add hl]; congr 1; ring]
      rw [show (((y.2 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.2 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η) by
            rw [← Real.rpow_add hr]; congr 1; ring]
      dsimp only [K]
      ring
    _ = K * hughesYoungCommonDivisorMajorant A C y := by
      rw [mul_rpow_commonDivisorMajorant_eq]
      congr 2
      all_goals dsimp [A, C, θ]; ring
    _ ≤ K * hughesYoungPositivePairMajorant A C y := by
      gcongr
      exact hughesYoungCommonDivisorMajorant_le_pairMajorant hA hC y

/-- Quantitative pointwise majorization behind the preceding absolute
convergence theorem.  The fixed twist logarithms cost the additional
`h^η k^η` factor. -/
theorem norm_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y *
        hughesYoungDFIPositiveLogFactorLeft h y *
        hughesYoungDFIPositiveLogFactorRight k y‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  let θ : ℝ := 1 / 2 + 2 * η
  let A : ℝ := 1 + 2 * η
  let C : ℝ := 1 - 2 * η
  let B : ℝ := 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|
  let K : ℝ := ((h : ℝ) ^ θ * (k : ℝ) ^ θ) * B ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hθ : 1 / 2 < θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hA : 1 < A := by dsimp [A]; linarith
  have hterm := norm_hughesYoungEquation96PositiveTerm_one_one_le
    hh hk (show 0 ≤ θ by linarith [hθ]) hθ1 (1 : ℂ) y
  have hterm' :
      ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ ≤
        ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y := by
    convert hterm using 1
    all_goals norm_num
  have hleft := norm_hughesYoungDFIPositiveLogFactorLeft_le hη hh y
  have hright := norm_hughesYoungDFIPositiveLogFactorRight_le hη hk y
  have hcommon0 : 0 ≤ hughesYoungCommonDivisorMajorant (2 * θ) 1 y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hpow0 : 0 ≤ (((y.1 : ℕ) : ℝ) ^ η * (((y.2 : ℕ) : ℝ) ^ η)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  rw [norm_mul, norm_mul]
  calc
    ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ *
        ‖hughesYoungDFIPositiveLogFactorLeft h y‖ *
        ‖hughesYoungDFIPositiveLogFactorRight k y‖ ≤
      (((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y) *
        (B * (h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) *
        (B * (k : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) := by
      gcongr
    _ = K *
        (((((y.1 : ℕ) : ℝ) ^ (2 * η)) *
            (((y.2 : ℕ) : ℝ) ^ (2 * η))) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y) := by
      have hl : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
      have hr : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
      rw [show (((y.1 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.1 : ℕ) : ℝ) ^ η) * (((y.1 : ℕ) : ℝ) ^ η) by
            rw [← Real.rpow_add hl]; congr 1; ring]
      rw [show (((y.2 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.2 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η) by
            rw [← Real.rpow_add hr]; congr 1; ring]
      dsimp only [K]
      ring
    _ = K * hughesYoungCommonDivisorMajorant A C y := by
      rw [mul_rpow_commonDivisorMajorant_eq]
      congr 2
      all_goals dsimp [A, C, θ]; ring
    _ ≤ K * hughesYoungPositivePairMajorant A C y := by
      have hK : 0 ≤ K := by dsimp [K, B]; positivity
      exact mul_le_mul_of_nonneg_left
        (hughesYoungCommonDivisorMajorant_le_pairMajorant hA
          (show 0 < C by dsimp [C]; linarith) y) hK
    _ = _ := by rfl

/-- Explicit uniform bound for the complete twice-logarithmic equation-(96)
series on `Re w = 1`. -/
theorem norm_tsum_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hs := summable_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors
    hh hk hη hη4
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  calc
    _ ≤ ∑' y : ℕ+ × ℕ+,
        ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' y : ℕ+ × ℕ+,
        K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y :=
      hs.norm.tsum_le_tsum
        (fun y => norm_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors_le
          hh hk hη hη4 y) hm
    _ = _ := by
      rw [tsum_mul_left]

noncomputable def hughesYoungDFIPositiveLogSelectorLeft
    (i : Bool) (h : ℕ) (y : ℕ+ × ℕ+) : ℂ :=
  if i then hughesYoungDFIPositiveLogFactorLeft h y else 1

noncomputable def hughesYoungDFIPositiveLogSelectorRight
    (j : Bool) (k : ℕ) (y : ℕ+ × ℕ+) : ℂ :=
  if j then hughesYoungDFIPositiveLogFactorRight k y else 1

theorem norm_hughesYoungDFIPositiveLogSelectorLeft_le
    (i : Bool) {η : ℝ} (hη : 0 < η) {h : ℕ} (hh : 0 < h)
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungDFIPositiveLogSelectorLeft i h y‖ ≤
      (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) *
        (h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η := by
  let B : ℝ := 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hl1 : (1 : ℝ) ≤ (y.1 : ℕ) := by exact_mod_cast y.1.2
  have hr1 : (1 : ℝ) ≤ (y.2 : ℕ) := by exact_mod_cast y.2.2
  have hp : 1 ≤ (h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η *
      ((y.2 : ℕ) : ℝ) ^ η := by
    have hhp := Real.one_le_rpow hh1 hη.le
    have hlp := Real.one_le_rpow hl1 hη.le
    have hrp := Real.one_le_rpow hr1 hη.le
    nlinarith [mul_le_mul hhp hlp (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith [hhp]),
      mul_le_mul (mul_le_mul hhp hlp (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith [hhp])) hrp (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (by positivity) _))]
  cases i with
  | false =>
      simp only [hughesYoungDFIPositiveLogSelectorLeft, Bool.false_eq_true,
        ↓reduceIte, norm_one]
      have hD : 1 ≤ 1 + B := by linarith
      calc
        1 ≤ (1 + B) * ((h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η *
            ((y.2 : ℕ) : ℝ) ^ η) := by nlinarith
        _ = _ := by dsimp [B]; ring
  | true =>
      simp only [hughesYoungDFIPositiveLogSelectorLeft, ↓reduceIte]
      have hs := norm_hughesYoungDFIPositiveLogFactorLeft_le hη hh y
      calc
        _ ≤ B * ((h : ℝ) ^ η *
            (((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η)) := by
          simpa only [B, mul_assoc] using hs
        _ ≤ (1 + B) * ((h : ℝ) ^ η *
            (((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η)) := by
          gcongr
          linarith
        _ = _ := by dsimp [B]; ring

theorem norm_hughesYoungDFIPositiveLogSelectorRight_le
    (j : Bool) {η : ℝ} (hη : 0 < η) {k : ℕ} (hk : 0 < k)
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) *
        (k : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η := by
  simpa only [hughesYoungDFIPositiveLogSelectorRight,
    hughesYoungDFIPositiveLogSelectorLeft,
    hughesYoungDFIPositiveLogFactorRight,
    hughesYoungDFIPositiveLogFactorLeft,
    hughesYoungEquation96PositiveLogB,
    hughesYoungEquation96PositiveLogA] using
      norm_hughesYoungDFIPositiveLogSelectorLeft_le j hη hk y

theorem norm_hughesYoungEquation96PositiveTerm_mul_logSelectors_le
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  let θ : ℝ := 1 / 2 + 2 * η
  let A : ℝ := 1 + 2 * η
  let C : ℝ := 1 - 2 * η
  let D : ℝ := 1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|
  let K : ℝ := ((h : ℝ) ^ θ * (k : ℝ) ^ θ) * D ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hθ : 1 / 2 < θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
  have hA : 1 < A := by dsimp [A]; linarith
  have hterm := norm_hughesYoungEquation96PositiveTerm_one_one_le
    hh hk (show 0 ≤ θ by linarith [hθ]) hθ1 (1 : ℂ) y
  have hterm' :
      ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ ≤
        ((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y := by
    convert hterm using 1
    all_goals norm_num
  have hleft := norm_hughesYoungDFIPositiveLogSelectorLeft_le i hη hh y
  have hright := norm_hughesYoungDFIPositiveLogSelectorRight_le j hη hk y
  have hcommon0 : 0 ≤ hughesYoungCommonDivisorMajorant (2 * θ) 1 y := by
    unfold hughesYoungCommonDivisorMajorant
    positivity
  have hpow0 : 0 ≤ (((y.1 : ℕ) : ℝ) ^ η * (((y.2 : ℕ) : ℝ) ^ η)) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  rw [norm_mul, norm_mul]
  calc
    ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ *
        ‖hughesYoungDFIPositiveLogSelectorLeft i h y‖ *
        ‖hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (((h : ℝ) ^ θ * (k : ℝ) ^ θ) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y) *
        (D * (h : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) *
        (D * (k : ℝ) ^ η * ((y.1 : ℕ) : ℝ) ^ η * ((y.2 : ℕ) : ℝ) ^ η) := by
      gcongr
    _ = K *
        (((((y.1 : ℕ) : ℝ) ^ (2 * η)) *
            (((y.2 : ℕ) : ℝ) ^ (2 * η))) *
          hughesYoungCommonDivisorMajorant (2 * θ) 1 y) := by
      have hl : 0 < (((y.1 : ℕ) : ℝ)) := by exact_mod_cast y.1.2
      have hr : 0 < (((y.2 : ℕ) : ℝ)) := by exact_mod_cast y.2.2
      rw [show (((y.1 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.1 : ℕ) : ℝ) ^ η) * (((y.1 : ℕ) : ℝ) ^ η) by
            rw [← Real.rpow_add hl]; congr 1; ring]
      rw [show (((y.2 : ℕ) : ℝ) ^ (2 * η)) =
          (((y.2 : ℕ) : ℝ) ^ η) * (((y.2 : ℕ) : ℝ) ^ η) by
            rw [← Real.rpow_add hr]; congr 1; ring]
      dsimp only [K]
      ring
    _ = K * hughesYoungCommonDivisorMajorant A C y := by
      rw [mul_rpow_commonDivisorMajorant_eq]
      congr 2
      all_goals dsimp [A, C, θ]; ring
    _ ≤ K * hughesYoungPositivePairMajorant A C y := by
      have hK : 0 ≤ K := by dsimp [K, D]; positivity
      exact mul_le_mul_of_nonneg_left
        (hughesYoungCommonDivisorMajorant_le_pairMajorant hA
          (show 0 < C by dsimp [C]; linarith) y) hK
    _ = _ := by rfl

theorem summable_hughesYoungEquation96PositiveTerm_mul_logSelectors
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1 2 y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y) := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  exact Summable.of_norm_bounded hm fun y =>
    norm_hughesYoungEquation96PositiveTerm_mul_logSelectors_le
      i j hh hk hη hη4 y

theorem norm_tsum_hughesYoungEquation96PositiveTerm_mul_logSelectors_le
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          hughesYoungDFIPositiveLogSelectorLeft i h y *
          hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hs := summable_hughesYoungEquation96PositiveTerm_mul_logSelectors
    i j hh hk hη hη4
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  calc
    _ ≤ ∑' y : ℕ+ × ℕ+,
        ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          hughesYoungDFIPositiveLogSelectorLeft i h y *
          hughesYoungDFIPositiveLogSelectorRight j k y‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' y : ℕ+ × ℕ+,
        K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y :=
      hs.norm.tsum_le_tsum
        (fun y => norm_hughesYoungEquation96PositiveTerm_mul_logSelectors_le
          i j hh hk hη hη4 y) hm
    _ = _ := by rw [tsum_mul_left]

/-- Moving vertically on the equation-(96) source line changes only the
phase of the positive-shift coordinate. -/
theorem norm_hughesYoungEquation96PositiveTerm_vertical_eq
    (h k : ℕ) (u : ℝ) (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1
        ((2 : ℂ) + (2 * u : ℂ) * I) y‖ =
      ‖hughesYoungEquation96PositiveTerm h k 1 1 2 y‖ := by
  unfold hughesYoungEquation96PositiveTerm
  simp only [norm_div, norm_mul]
  congr 2
  change ‖(((y.2 : ℕ) : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I))‖ =
    ‖(((y.2 : ℕ) : ℂ) ^ (2 : ℂ))‖
  rw [show (((y.2 : ℕ) : ℂ)) = ((((y.2 : ℕ) : ℝ) : ℂ)) by norm_num]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (show 0 < ((y.2 : ℕ) : ℝ) by exact_mod_cast y.2.2),
    Complex.norm_cpow_eq_rpow_re_of_pos
      (show 0 < ((y.2 : ℕ) : ℝ) by exact_mod_cast y.2.2)]
  norm_num

theorem norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
    (i j : Bool) (u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    (y : ℕ+ × ℕ+) :
    ‖hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  rw [norm_mul, norm_mul,
    norm_hughesYoungEquation96PositiveTerm_vertical_eq h k u y]
  simpa only [norm_mul] using
    norm_hughesYoungEquation96PositiveTerm_mul_logSelectors_le
      i j hh hk hη hη4 y

theorem summable_hughesYoungEquation96VerticalTerm_mul_logSelectors
    (i j : Bool) (u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft i h y *
        hughesYoungDFIPositiveLogSelectorRight j k y) := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  exact Summable.of_norm_bounded hm fun y =>
    norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
      i j u hh hk hη hη4 y

theorem norm_tsum_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
    (i j : Bool) (u : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft i h y *
          hughesYoungDFIPositiveLogSelectorRight j k y‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hs := summable_hughesYoungEquation96VerticalTerm_mul_logSelectors
    i j u hh hk hη hη4
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  calc
    _ ≤ ∑' y : ℕ+ × ℕ+,
        ‖hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft i h y *
          hughesYoungDFIPositiveLogSelectorRight j k y‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' y : ℕ+ × ℕ+,
        K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y :=
      hs.norm.tsum_le_tsum
        (fun y => norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
          i j u hh hk hη hη4 y) hm
    _ = _ := by rw [tsum_mul_left]

end RiemannZeta.GuthMaynard
