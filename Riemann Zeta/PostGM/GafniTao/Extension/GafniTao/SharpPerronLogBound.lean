import GafniTao.SharpPerronArithmetic

/-!
# The `y log^2 y / T` sharp-Perron bound

This file absorbs the two exact arithmetic majorants into the classical
logarithmic remainder.  All constants are produced explicitly from the
frozen logarithmic-derivative bound and `log 2`.
-/

namespace GafniTao

private theorem harmonic_floor_succ_le_log_halfPoint
    {x : ℝ} (hy : 2 ≤ sharpPerronHalfPoint x) :
    (harmonic (⌊x⌋₊ + 1) : ℝ) ≤
      (2 + 1 / Real.log 2) * Real.log (sharpPerronHalfPoint x) := by
  let y := sharpPerronHalfPoint x
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2y : Real.log 2 ≤ Real.log y :=
    Real.log_le_log (by norm_num) hy
  have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * y := by
    dsimp [y]
    rw [sharpPerronHalfPoint]
    push_cast
    linarith
  have hlogCast : Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤
      Real.log (2 * y) := by
    apply Real.log_le_log
    · positivity
    · exact hcast
  have hlogMul : Real.log (2 * y) = Real.log 2 + Real.log y := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy0.ne']
  have hone : 1 ≤ (1 / Real.log 2) * Real.log y := by
    rw [one_div_mul_eq_div, le_div_iff₀ hlog2]
    simpa [mul_comm] using hlog2y
  calc
    (harmonic (⌊x⌋₊ + 1) : ℝ) ≤
        1 + Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
      harmonic_le_one_add_log (⌊x⌋₊ + 1)
    _ ≤ 1 + Real.log (2 * y) := add_le_add le_rfl hlogCast
    _ ≤ (1 / Real.log 2) * Real.log y + 2 * Real.log y := by
      rw [hlogMul]
      linarith
    _ = (2 + 1 / Real.log 2) * Real.log y := by ring

private theorem log_two_mul_halfPoint_le_two_log_halfPoint
    {x : ℝ} (hy : 2 ≤ sharpPerronHalfPoint x) :
    Real.log (2 * sharpPerronHalfPoint x) ≤
      2 * Real.log (sharpPerronHalfPoint x) := by
  have hy0 : 0 < sharpPerronHalfPoint x := by linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy0.ne']
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hy
  linarith

private theorem log_le_log_sq_div_log_two
    {y : ℝ} (hy : 2 ≤ y) :
    Real.log y ≤ (Real.log y) ^ 2 / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log y :=
    Real.log_le_log (by norm_num) hy
  rw [le_div_iff₀ hlog2]
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  nlinarith

/-- The optimized right-line integral differs from `psi` at the half-integral
point by `O(y log^2 y / T)`, with a uniform positive constant. -/
theorem exists_norm_optimized_halfPoint_Perron_sub_psi_le :
    ∃ D : ℝ, 0 < D ∧ ∀ {T x : ℝ},
      2 ≤ sharpPerronHalfPoint x → 0 < T →
      ‖(1 / (2 * Real.pi) : ℂ) *
            (∫ t in (-T)..T,
              (-deriv riemannZeta
                  ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                    (t : ℂ) * Complex.I) /
                  riemannZeta
                    ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                      (t : ℂ) * Complex.I)) *
                (sharpPerronHalfPoint x : ℂ) ^
                  ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                    (t : ℂ) * Complex.I) /
                  ((sharpPerronAbscissa (sharpPerronHalfPoint x) : ℂ) +
                    (t : ℂ) * Complex.I)) -
          (Chebyshev.psi (sharpPerronHalfPoint x) : ℂ)‖ ≤
        D * sharpPerronHalfPoint x *
          (Real.log (sharpPerronHalfPoint x)) ^ 2 / T := by
  obtain ⟨C, hC, hSeries⟩ := exists_tsum_vonMangoldt_optimized_le
  let KH : ℝ := 2 + 1 / Real.log 2
  let KS : ℝ := 1 + C / Real.log 2
  let N : ℝ := 16 * sharpPerronRatioBound * KH +
    2 * Real.exp 1 * KS / Real.log 2
  let D : ℝ := N / Real.pi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKH : 0 < KH := by dsimp [KH]; positivity
  have hKS : 0 < KS := by dsimp [KS]; positivity
  have hR : 0 < sharpPerronRatioBound :=
    lt_of_lt_of_le zero_lt_one one_le_sharpPerronRatioBound
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 < D := div_pos hN Real.pi_pos
  refine ⟨D, hD, ?_⟩
  intro T x hy hT
  let y := sharpPerronHalfPoint x
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hden : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hH := harmonic_floor_succ_le_log_halfPoint hy
  have hlogTwo := log_two_mul_halfPoint_le_two_log_halfPoint hy
  have hlogSq := log_le_log_sq_div_log_two hy
  have hS0 : 0 ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ sharpPerronAbscissa y) := by
    exact tsum_nonneg (fun n => div_nonneg
      ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hSeriesY := hSeries y (by linarith)
  have hSeriesScaled :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ sharpPerronAbscissa y)) ≤ KS * Real.log y := by
    have hCscale : C ≤ (C / Real.log 2) * Real.log y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hy]
    calc
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ sharpPerronAbscissa y)) ≤ Real.log y + C := hSeriesY
      _ ≤ Real.log y + (C / Real.log 2) * Real.log y :=
        add_le_add le_rfl hCscale
      _ = KS * Real.log y := by dsimp [KS]; ring
  have hraw := norm_optimized_halfPoint_Perron_sub_psi_le_arithmetic hy hT
  have hnear :
      (sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
          (Real.pi * T)) *
          (4 * (harmonic (⌊x⌋₊ + 1) : ℝ)) ≤
        (16 * sharpPerronRatioBound * KH) * y *
          (Real.log y) ^ 2 / (Real.pi * T) := by
    have hprod :
        Real.log (2 * y) * (harmonic (⌊x⌋₊ + 1) : ℝ) ≤
          2 * KH * (Real.log y) ^ 2 := by
      have hharm : 0 ≤ (harmonic (⌊x⌋₊ + 1) : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      exact (mul_le_mul hlogTwo hH hharm
        (mul_nonneg (by norm_num) hlogy0)).trans_eq (by ring)
    rw [show
      (sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
          (Real.pi * T)) *
          (4 * (harmonic (⌊x⌋₊ + 1) : ℝ)) =
        (8 * sharpPerronRatioBound * y) *
          (Real.log (2 * y) * (harmonic (⌊x⌋₊ + 1) : ℝ)) /
            (Real.pi * T) by ring]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      (8 * sharpPerronRatioBound * y) *
          (Real.log (2 * y) * (harmonic (⌊x⌋₊ + 1) : ℝ)) ≤
        (8 * sharpPerronRatioBound * y) *
          (2 * KH * (Real.log y) ^ 2) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (16 * sharpPerronRatioBound * KH) * y *
          (Real.log y) ^ 2 := by ring
  have hfar :
      (2 * (y ^ sharpPerronAbscissa y) / (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa y)) ≤
        (2 * Real.exp 1 * KS / Real.log 2) * y *
          (Real.log y) ^ 2 / (Real.pi * T) := by
    rw [rpow_sharpPerronAbscissa (by linarith)]
    rw [show
      (2 * (Real.exp 1 * y) / (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa y)) =
        (2 * Real.exp 1 * y) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa y)) /
            (Real.pi * T) by ring]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      (2 * Real.exp 1 * y) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa y)) ≤
        (2 * Real.exp 1 * y) * (KS * Real.log y) :=
          mul_le_mul_of_nonneg_left hSeriesScaled (by positivity)
      _ ≤ (2 * Real.exp 1 * KS / Real.log 2) * y *
          (Real.log y) ^ 2 := by
            have hcoef : 0 ≤ 2 * Real.exp 1 * KS * y := by positivity
            calc
              (2 * Real.exp 1 * y) * (KS * Real.log y) =
                  (2 * Real.exp 1 * KS * y) * Real.log y := by ring
              _ ≤ (2 * Real.exp 1 * KS * y) *
                  ((Real.log y) ^ 2 / Real.log 2) :=
                    mul_le_mul_of_nonneg_left hlogSq hcoef
              _ = (2 * Real.exp 1 * KS / Real.log 2) * y *
                  (Real.log y) ^ 2 := by ring
  refine hraw.trans (add_le_add hnear hfar) |>.trans ?_
  change
    (16 * sharpPerronRatioBound * KH) * y * (Real.log y) ^ 2 /
          (Real.pi * T) +
        (2 * Real.exp 1 * KS / Real.log 2) * y * (Real.log y) ^ 2 /
          (Real.pi * T) ≤
      D * y * (Real.log y) ^ 2 / T
  dsimp [D, N]
  field_simp [Real.pi_ne_zero, hT.ne']
  exact le_rfl

end GafniTao
