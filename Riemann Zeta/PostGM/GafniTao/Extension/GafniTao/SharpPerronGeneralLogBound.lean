import GafniTao.SharpPerronGeneralArithmetic

/-!
# Uniform logarithmic sharp-Perron bound at an arbitrary real endpoint

This file absorbs the explicit transition, harmonic, and Dirichlet-tail
majorants from `SharpPerronGeneralArithmetic` into `x log^2 x / T`.  The
height assumptions are the ones used by the contour shift: `8 ≤ T ≤ x`.
-/

namespace GafniTao

private theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

private theorem two_le_log {x : ℝ} (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  apply (Real.le_log_iff_exp_le (by linarith)).2
  exact exp_two_le_eight.trans hx

private theorem log_two_mul_le_two_log {x : ℝ} (hx : 8 ≤ x) :
    Real.log (2 * x) ≤ 2 * Real.log x := by
  have hx0 : 0 < x := by linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
  have hlog2x : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) (by linarith)
  linarith

private theorem harmonic_floor_succ_le_three_log {x : ℝ} (hx : 8 ≤ x) :
    (harmonic (⌊x⌋₊ + 1) : ℝ) ≤ 3 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * x := by
    push_cast
    have hfloor := Nat.floor_le hx0.le
    linarith
  have hlogCast : Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (2 * x) := by
    apply Real.log_le_log
    · positivity
    · exact hcast
  calc
    (harmonic (⌊x⌋₊ + 1) : ℝ) ≤
        1 + Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
      harmonic_le_one_add_log (⌊x⌋₊ + 1)
    _ ≤ 1 + Real.log (2 * x) := add_le_add le_rfl hlogCast
    _ ≤ 3 * Real.log x := by
      have htwo := two_le_log hx
      have hmul := log_two_mul_le_two_log hx
      linarith

private theorem abscissa_add_height_le_two_mul
    {x T : ℝ} (hx : 8 ≤ x) (hTx : T ≤ x + 1) :
    sharpPerronAbscissa x + T ≤ 2 * x := by
  have hlog : 2 ≤ Real.log x := two_le_log hx
  have hinv : 1 / Real.log x ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hlog
  rw [sharpPerronAbscissa]
  linarith

private theorem transition_log_difference_le_two_log
    {x T : ℝ} (hx : 8 ≤ x) (hT : 0 < T) (hTx : T ≤ x + 1) :
    Real.log (sharpPerronAbscissa x + T) -
        Real.log (sharpPerronAbscissa x) ≤ 2 * Real.log x := by
  have hcOne : 1 < sharpPerronAbscissa x :=
    one_lt_sharpPerronAbscissa (by linarith)
  have hcLog : 0 ≤ Real.log (sharpPerronAbscissa x) :=
    Real.log_nonneg hcOne.le
  have hsumPos : 0 < sharpPerronAbscissa x + T := by linarith
  have hsum := Real.log_le_log hsumPos
    (abscissa_add_height_le_two_mul hx hTx)
  have hmul := log_two_mul_le_two_log hx
  linarith

/-- The right-line Perron integral approximates `psi x` uniformly at every
real endpoint in the contour range. -/
theorem exists_norm_optimized_general_Perron_sub_psi_le :
    ∃ D : ℝ, 0 < D ∧ ∀ {T x : ℝ},
      8 ≤ x → 8 ≤ T → T ≤ x + 1 →
      ‖(1 / (2 * Real.pi) : ℂ) *
            (∫ t in (-T)..T,
              (-deriv riemannZeta
                  ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I) /
                  riemannZeta
                    ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I)) *
                (x : ℂ) ^
                  ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I) /
                  ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I)) -
          (Chebyshev.psi x : ℂ)‖ ≤
        D * x * (Real.log x) ^ 2 / T := by
  obtain ⟨C, hC, hSeries⟩ := exists_tsum_vonMangoldt_optimized_le
  let KS : ℝ := 1 + C / Real.log 2
  let D : ℝ :=
    8 * (4 * sharpPerronRatioBound / Real.pi + 1) +
      96 * sharpPerronRatioBound / Real.pi +
      2 * Real.exp 1 * KS / Real.pi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKS : 0 < KS := by dsimp [KS]; positivity
  have hR : 0 < sharpPerronRatioBound :=
    lt_of_lt_of_le zero_lt_one one_le_sharpPerronRatioBound
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro T x hx hT hTx
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog1 : 1 ≤ Real.log x := (by linarith [two_le_log hx])
  have hden : 0 < Real.pi * T := mul_pos Real.pi_pos hT0
  have hlogTwo := log_two_mul_le_two_log hx
  have hdiff := transition_log_difference_le_two_log hx hT0 hTx
  have hH := harmonic_floor_succ_le_three_log hx
  have hSeriesX := hSeries x (by linarith)
  have hSeriesScaled :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ sharpPerronAbscissa x)) ≤ KS * Real.log x := by
    have hCscale : C ≤ (C / Real.log 2) * Real.log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ x)]
    calc
      _ ≤ Real.log x + C := hSeriesX
      _ ≤ Real.log x + (C / Real.log 2) * Real.log x :=
        add_le_add le_rfl hCscale
      _ = KS * Real.log x := by dsimp [KS]; ring
  have hraw := norm_optimized_general_Perron_sub_psi_le_arithmetic
    (T := T) (x := x) (by linarith) hT0
  have htransition :
      (Real.log (2 * x) *
          (sharpPerronRatioBound * (2 / Real.pi) *
            (Real.log (sharpPerronAbscissa x + T) -
              Real.log (sharpPerronAbscissa x)) + 1)) * 2 ≤
        (8 * (4 * sharpPerronRatioBound / Real.pi + 1)) *
          x * Real.log x ^ 2 / T := by
    have hinside :
        sharpPerronRatioBound * (2 / Real.pi) *
              (Real.log (sharpPerronAbscissa x + T) -
                Real.log (sharpPerronAbscissa x)) + 1 ≤
            (4 * sharpPerronRatioBound / Real.pi + 1) * Real.log x := by
      have hcoef : 0 ≤ sharpPerronRatioBound * (2 / Real.pi) := by positivity
      calc
        _ ≤ sharpPerronRatioBound * (2 / Real.pi) * (2 * Real.log x) + 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hdiff hcoef) le_rfl
        _ = (4 * sharpPerronRatioBound / Real.pi) * Real.log x + 1 := by ring
        _ ≤ (4 * sharpPerronRatioBound / Real.pi) * Real.log x + Real.log x :=
          add_le_add le_rfl hlog1
        _ = (4 * sharpPerronRatioBound / Real.pi + 1) * Real.log x := by ring
    have hinside0 : 0 ≤
        sharpPerronRatioBound * (2 / Real.pi) *
              (Real.log (sharpPerronAbscissa x + T) -
                Real.log (sharpPerronAbscissa x)) + 1 := by
      have hc : 0 < sharpPerronAbscissa x :=
        sharpPerronAbscissa_pos (by linarith)
      have hdiff0 : 0 ≤ Real.log (sharpPerronAbscissa x + T) -
          Real.log (sharpPerronAbscissa x) := by
        rw [sub_nonneg, Real.log_le_log_iff hc (by linarith)]
        linarith
      positivity
    have hleft :
        (Real.log (2 * x) *
            (sharpPerronRatioBound * (2 / Real.pi) *
              (Real.log (sharpPerronAbscissa x + T) -
                Real.log (sharpPerronAbscissa x)) + 1)) * 2 ≤
          4 * (4 * sharpPerronRatioBound / Real.pi + 1) *
            Real.log x ^ 2 := by
      have hmul := mul_le_mul hlogTwo hinside hinside0 (by positivity)
      nlinarith [hmul]
    calc
      _ ≤ 4 * (4 * sharpPerronRatioBound / Real.pi + 1) *
          Real.log x ^ 2 := hleft
      _ ≤ (8 * (4 * sharpPerronRatioBound / Real.pi + 1)) *
          x * Real.log x ^ 2 / T := by
        rw [le_div_iff₀ hT0]
        have hcoef : 0 ≤ 4 * (4 * sharpPerronRatioBound / Real.pi + 1) := by
          positivity
        have htwoX : x + 1 ≤ 2 * x := by linarith
        nlinarith [mul_le_mul_of_nonneg_left (hTx.trans htwoX) hcoef]
  have hnear :
      (sharpPerronRatioBound * Real.log (2 * x) * (2 * x) /
          (Real.pi * T)) *
          (8 * (harmonic (⌊x⌋₊ + 1) : ℝ)) ≤
        (96 * sharpPerronRatioBound / Real.pi) * x *
          Real.log x ^ 2 / T := by
    rw [show
      (sharpPerronRatioBound * Real.log (2 * x) * (2 * x) /
          (Real.pi * T)) * (8 * (harmonic (⌊x⌋₊ + 1) : ℝ)) =
        (16 * sharpPerronRatioBound * x) *
          (Real.log (2 * x) * (harmonic (⌊x⌋₊ + 1) : ℝ)) /
            (Real.pi * T) by ring]
    rw [show
      (96 * sharpPerronRatioBound / Real.pi) * x * Real.log x ^ 2 / T =
        (96 * sharpPerronRatioBound * x * Real.log x ^ 2) /
          (Real.pi * T) by ring]
    apply div_le_div_of_nonneg_right _ hden.le
    have hprod :
        Real.log (2 * x) * (harmonic (⌊x⌋₊ + 1) : ℝ) ≤
          6 * Real.log x ^ 2 := by
      have hH0 : 0 ≤ (harmonic (⌊x⌋₊ + 1) : ℝ) := by
        simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      exact (mul_le_mul hlogTwo hH hH0 (by positivity)).trans_eq (by ring)
    have hcoefNear : 0 ≤ 16 * sharpPerronRatioBound * x := by positivity
    exact (mul_le_mul_of_nonneg_left hprod hcoefNear).trans_eq (by ring)
  have hfar :
      (2 * x ^ sharpPerronAbscissa x / (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa x)) ≤
        (2 * Real.exp 1 * KS / Real.pi) * x *
          Real.log x ^ 2 / T := by
    rw [rpow_sharpPerronAbscissa (by linarith : 1 < x)]
    rw [show
      (2 * (Real.exp 1 * x) / (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa x)) =
        (2 * Real.exp 1 * x) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            ((n : ℝ) ^ sharpPerronAbscissa x)) / (Real.pi * T) by ring]
    rw [show
      (2 * Real.exp 1 * KS / Real.pi) * x * Real.log x ^ 2 / T =
        (2 * Real.exp 1 * KS * x * Real.log x ^ 2) /
          (Real.pi * T) by ring]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _ ≤ (2 * Real.exp 1 * x) * (KS * Real.log x) :=
        mul_le_mul_of_nonneg_left hSeriesScaled (by positivity)
      _ ≤ 2 * Real.exp 1 * KS * x * Real.log x ^ 2 := by
        have hcoef : 0 ≤ 2 * Real.exp 1 * KS * x := by positivity
        calc
          (2 * Real.exp 1 * x) * (KS * Real.log x) =
              (2 * Real.exp 1 * KS * x) * Real.log x := by ring
          _ ≤ (2 * Real.exp 1 * KS * x) * Real.log x ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            nlinarith [sq_nonneg (Real.log x - 1)]
  refine hraw.trans (add_le_add (add_le_add htransition hnear) hfar) |>.trans ?_
  dsimp [D]
  ring_nf
  exact le_rfl

end GafniTao
