import TaoTrudgianYang2025.ZetaAtkinsonTwoTermSource

/-!
# Square-root coordinates for both actual Atkinson carriers

The divisor frequency enters linearly. The normalized phase has
curvature at most minus two, and its slope is factored at the
actual positive saddle. No stationary approximation is assumed.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def atkinsonRootPhase (T b y : ℝ) : ℝ :=
  (T / Real.pi) * Real.log y - y ^ 2 + 2 * b * y

def atkinsonRootSlope (T b y : ℝ) : ℝ :=
  T / (Real.pi * y) - 2 * y + 2 * b

theorem zetaAtkinsonPhase_sq (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    zetaAtkinsonPhase T b (y ^ 2) = 2 * Real.pi * atkinsonRootPhase T b y := by
  rw [zetaAtkinsonPhase, Real.log_pow, Real.sqrt_sq hy.le]
  unfold atkinsonRootPhase
  field_simp
  ring

theorem contDiffAt_atkinsonRootPhase (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ 2 (atkinsonRootPhase T b) y := by
  unfold atkinsonRootPhase
  fun_prop (disch := exact hy.ne')

theorem hasDerivAt_atkinsonRootPhase (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (atkinsonRootPhase T b) (atkinsonRootSlope T b y) y := by
  have h := (((Real.hasDerivAt_log hy.ne').const_mul (T / Real.pi)).sub
    ((hasDerivAt_id y).pow 2)).add ((hasDerivAt_id y).const_mul (2 * b))
  convert h using 1
  unfold atkinsonRootSlope
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

theorem hasDerivAt_atkinsonRootSlope (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (atkinsonRootSlope T b) (-T / (Real.pi * y ^ 2) - 2) y := by
  have h := ((((hasDerivAt_const y (T / Real.pi)).div (hasDerivAt_id y) hy.ne').sub
    ((hasDerivAt_id y).const_mul 2)).add_const (2 * b))
  convert h using 1
  · funext z
    unfold atkinsonRootSlope
    dsimp
    ring
  · simp only [id_eq, zero_mul, mul_one, zero_sub]
    ring

theorem atkinsonRootSlope_strictAnti {T : ℝ} (hT : 0 ≤ T) (b : ℝ) :
    StrictAntiOn (atkinsonRootSlope T b) (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hdiv : T / (Real.pi * y) ≤ T / (Real.pi * x) :=
    div_le_div_of_nonneg_left hT (by positivity) (by nlinarith [Real.pi_pos])
  unfold atkinsonRootSlope
  linarith

theorem atkinsonRootSlope_factored {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    atkinsonRootSlope T b y =
      2 * (atkinsonSaddleRoot (T / (2 * Real.pi)) b - y) *
        (1 + (atkinsonSaddleRoot (T / (2 * Real.pi)) b - b) / y) := by
  have h := atkinsonSaddleRoot_equation (by positivity : 0 < T / (2 * Real.pi)) b
  have he := (eq_div_iff (by positivity : (2 * Real.pi : ℝ) ≠ 0)).mp h
  generalize atkinsonSaddleRoot (T / (2 * Real.pi)) b = r at *
  unfold atkinsonRootSlope
  field_simp
  nlinarith

theorem atkinsonRootSlope_le_neg_two {T b y : ℝ} (hT : 0 < T) (hy : 0 < y)
    (hr : atkinsonSaddleRoot (T / (2 * Real.pi)) b + 1 ≤ y) :
    atkinsonRootSlope T b y ≤ -2 := by
  rw [atkinsonRootSlope_factored hT b hy]
  have hp := atkinsonSaddleRoot_sub_pos (by positivity : 0 < T / (2 * Real.pi)) b
  have hq : 0 ≤ (atkinsonSaddleRoot (T / (2 * Real.pi)) b - b) / y := by positivity
  nlinarith [mul_nonpos_of_nonpos_of_nonneg
    (show atkinsonSaddleRoot (T / (2 * Real.pi)) b - y ≤ 0 by linarith) hq]

theorem two_le_atkinsonRootSlope {T b y : ℝ} (hT : 0 < T) (hy : 0 < y)
    (hr : y ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - 1) :
    2 ≤ atkinsonRootSlope T b y := by
  rw [atkinsonRootSlope_factored hT b hy]
  have hp := atkinsonSaddleRoot_sub_pos (by positivity : 0 < T / (2 * Real.pi)) b
  have hq : 0 ≤ (atkinsonSaddleRoot (T / (2 * Real.pi)) b - b) / y := by positivity
  nlinarith [mul_nonneg
    (show 0 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - y by linarith) hq]

end TaoTrudgianYang2025
