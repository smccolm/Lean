import Tao2026.SmoothNumberSaddleGaussianProduct
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Prime-local Taylor expansion at the smooth saddle

This module supplies the remaining prime-local input for fixed-frequency
Gaussian convergence.  It develops the first three moments of the geometric
prime-power law and uses them to control the centered characteristic factor.
-/

open Filter Topology

namespace Tao2026

noncomputable section

set_option maxHeartbeats 800000

/-- The second falling-factorial geometric series. -/
theorem hasSum_fallingTwo_mul_geometric {a : ℝ} (ha : |a| < 1) :
    HasSum (fun n : ℕ =>
      (n : ℝ) * (n - 1 : ℕ) * a ^ n)
      (2 * a ^ 2 / (1 - a) ^ 3) := by
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 2 (by simpa [Real.norm_eq_abs] using ha)
  have hdesc : HasSum (fun n : ℕ =>
      (((n + 2).descFactorial 2 : ℕ) : ℝ) * a ^ n)
      (2 / (1 - a) ^ 3) := by
    have hterm : HasSum (fun n : ℕ =>
        (((n + 2).descFactorial 2 : ℕ) : ℝ) * a ^ n)
        (2 * (1 / (1 - a) ^ (2 + 1))) :=
      (hchoose.mul_left (2 : ℝ)).congr_fun (fun n => by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        norm_num
        ring)
    convert hterm using 1
    norm_num
    ring
  have hshift : HasSum (fun n : ℕ =>
      ((n + 2 : ℕ) : ℝ) * (n + 1 : ℕ) * a ^ (n + 2))
      (2 * a ^ 2 / (1 - a) ^ 3) := by
    have hterm : HasSum (fun n : ℕ =>
        ((n + 2 : ℕ) : ℝ) * (n + 1 : ℕ) * a ^ (n + 2))
        (a ^ 2 * (2 / (1 - a) ^ 3)) :=
      (hdesc.mul_left (a ^ 2)).congr_fun (fun n => by
        rw [Nat.descFactorial_eq_prod_range]
        norm_num [Finset.prod_range_succ]
        rw [pow_add]
        ring)
    convert hterm using 1
    ring
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) * (n - 1 : ℕ) * a ^ n
  have hshiftF : HasSum (fun n => f (n + 2))
      (2 * a ^ 2 / (1 - a) ^ 3) := by
    refine hshift.congr_fun (fun n => ?_)
    dsimp only [f]
    have hsub : n + 2 - 1 = n + 1 := by omega
    rw [hsub]
  have hfull := (hasSum_nat_add_iff 2).mp hshiftF
  have hzero : ∑ i ∈ Finset.range 2, f i = 0 := by
    norm_num [f, Finset.sum_range_succ]
  rw [hzero, add_zero] at hfull
  exact hfull

/-- Exact second raw moment of a geometric series. -/
theorem hasSum_natCast_sq_mul_geometric {a : ℝ} (ha : |a| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * a ^ n)
      (a * (1 + a) / (1 - a) ^ 3) := by
  have hfall := hasSum_fallingTwo_mul_geometric ha
  have hfirst := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (by simpa [Real.norm_eq_abs] using ha)
  convert hfall.add hfirst using 1
  · ext n
    by_cases hn : n = 0
    · subst n
      simp
    · have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [Nat.cast_sub hnOne]
      push_cast
      ring
  · have hden : 1 - a ≠ 0 := by
      have := (lt_of_le_of_lt (le_abs_self a) ha)
      linarith
    field_simp [hden]
    ring

/-- The third falling-factorial geometric series. -/
theorem hasSum_fallingThree_mul_geometric {a : ℝ} (ha : |a| < 1) :
    HasSum (fun n : ℕ =>
      (n : ℝ) * (n - 1 : ℕ) * (n - 2 : ℕ) * a ^ n)
      (6 * a ^ 3 / (1 - a) ^ 4) := by
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 3 (by simpa [Real.norm_eq_abs] using ha)
  have hdesc : HasSum (fun n : ℕ =>
      (((n + 3).descFactorial 3 : ℕ) : ℝ) * a ^ n)
      (6 / (1 - a) ^ 4) := by
    have hterm : HasSum (fun n : ℕ =>
        (((n + 3).descFactorial 3 : ℕ) : ℝ) * a ^ n)
        (6 * (1 / (1 - a) ^ (3 + 1))) :=
      (hchoose.mul_left (6 : ℝ)).congr_fun (fun n => by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        norm_num
        ring)
    convert hterm using 1
    norm_num
    ring
  have hshift : HasSum (fun n : ℕ =>
      ((n + 3 : ℕ) : ℝ) * (n + 2 : ℕ) * (n + 1 : ℕ) *
        a ^ (n + 3))
      (6 * a ^ 3 / (1 - a) ^ 4) := by
    have hterm : HasSum (fun n : ℕ =>
        ((n + 3 : ℕ) : ℝ) * (n + 2 : ℕ) * (n + 1 : ℕ) *
          a ^ (n + 3)) (a ^ 3 * (6 / (1 - a) ^ 4)) :=
      (hdesc.mul_left (a ^ 3)).congr_fun (fun n => by
        rw [Nat.descFactorial_eq_prod_range]
        norm_num [Finset.prod_range_succ]
        rw [pow_add]
        ring)
    convert hterm using 1
    ring
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) * (n - 1 : ℕ) * (n - 2 : ℕ) * a ^ n
  have hshiftF : HasSum (fun n => f (n + 3))
      (6 * a ^ 3 / (1 - a) ^ 4) := by
    refine hshift.congr_fun (fun n => ?_)
    dsimp only [f]
    have hsubOne : n + 3 - 1 = n + 2 := by omega
    have hsubTwo : n + 3 - 2 = n + 1 := by omega
    rw [hsubOne, hsubTwo]
  have hfull := (hasSum_nat_add_iff 3).mp hshiftF
  have hzero : ∑ i ∈ Finset.range 3, f i = 0 := by
    norm_num [f, Finset.sum_range_succ]
  rw [hzero, add_zero] at hfull
  exact hfull

/-- Exact third raw moment of a geometric series. -/
theorem hasSum_natCast_cube_mul_geometric {a : ℝ} (ha : |a| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 3 * a ^ n)
      (a * (1 + 4 * a + a ^ 2) / (1 - a) ^ 4) := by
  have hthree := hasSum_fallingThree_mul_geometric ha
  have htwo := (hasSum_fallingTwo_mul_geometric ha).mul_left 3
  have hone := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (by simpa [Real.norm_eq_abs] using ha)
  convert (hthree.add htwo).add hone using 1
  · ext n
    by_cases hnTwo : 2 ≤ n
    · rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub hnTwo]
      push_cast
      ring
    · interval_cases n <;> norm_num
  · have hden : 1 - a ≠ 0 := by
      have := (lt_of_le_of_lt (le_abs_self a) ha)
      linarith
    field_simp [hden]
    ring

/-- Probability mass of the geometric prime-power exponent with ratio `a`. -/
noncomputable def saddleGeometricWeight (a : ℝ) (n : ℕ) : ℝ :=
  (1 - a) * a ^ n

/-- Mean exponent of the geometric prime-power law. -/
noncomputable def saddleGeometricMean (a : ℝ) : ℝ :=
  a / (1 - a)

/-- The geometric prime-power masses sum to one. -/
theorem hasSum_saddleGeometricWeight {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (saddleGeometricWeight a) 1 := by
  have hgeom := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (1 - a)
  have hden : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  convert hgeom using 1
  field_simp [hden]

/-- First raw moment of the geometric prime-power exponent. -/
theorem hasSum_saddleGeometricWeight_mul_natCast {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n : ℕ => saddleGeometricWeight a n * n)
      (saddleGeometricMean a) := by
  have haAbs : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have hraw := (hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (by simpa [Real.norm_eq_abs] using haAbs)).mul_left (1 - a)
  have hden : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  unfold saddleGeometricWeight saddleGeometricMean
  convert hraw using 1
  · ext n
    ring
  · field_simp [hden]

/-- Second raw moment of the geometric prime-power exponent. -/
theorem hasSum_saddleGeometricWeight_mul_natCast_sq {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n : ℕ => saddleGeometricWeight a n * (n : ℝ) ^ 2)
      (a * (1 + a) / (1 - a) ^ 2) := by
  have haAbs : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have hraw := (hasSum_natCast_sq_mul_geometric haAbs).mul_left (1 - a)
  have hden : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  unfold saddleGeometricWeight
  convert hraw using 1
  · ext n
    ring
  · field_simp [hden]

/-- Third raw moment of the geometric prime-power exponent. -/
theorem hasSum_saddleGeometricWeight_mul_natCast_cube {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n : ℕ => saddleGeometricWeight a n * (n : ℝ) ^ 3)
      (a * (1 + 4 * a + a ^ 2) / (1 - a) ^ 3) := by
  have haAbs : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have hraw := (hasSum_natCast_cube_mul_geometric haAbs).mul_left (1 - a)
  have hden : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  unfold saddleGeometricWeight
  convert hraw using 1
  · ext n
    ring
  · field_simp [hden]

/-- The centered geometric exponent has mean zero. -/
theorem hasSum_saddleGeometricWeight_mul_centered {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n : ℕ =>
      saddleGeometricWeight a n * ((n : ℝ) - saddleGeometricMean a)) 0 := by
  have hfirst := hasSum_saddleGeometricWeight_mul_natCast ha0 ha1
  have hmass := (hasSum_saddleGeometricWeight ha0 ha1).mul_left
    (saddleGeometricMean a)
  convert hfirst.sub hmass using 1
  · ext n
    ring
  · ring

/-- The centered geometric exponent has variance `a/(1-a)^2`. -/
theorem hasSum_saddleGeometricWeight_mul_centered_sq {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HasSum (fun n : ℕ =>
      saddleGeometricWeight a n *
        ((n : ℝ) - saddleGeometricMean a) ^ 2)
      (a / (1 - a) ^ 2) := by
  let μ := saddleGeometricMean a
  have htwo := hasSum_saddleGeometricWeight_mul_natCast_sq ha0 ha1
  have hone := (hasSum_saddleGeometricWeight_mul_natCast ha0 ha1).mul_left
    (2 * μ)
  have hmass := (hasSum_saddleGeometricWeight ha0 ha1).mul_left (μ ^ 2)
  have hden : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  convert (htwo.sub hone).add hmass using 1
  · ext n
    dsimp only [μ]
    ring
  · dsimp only [μ, saddleGeometricMean]
    field_simp [hden]
    ring

/-- Cubing the centered displacement costs at most four times the sum of the
two nonnegative cubes. -/
theorem abs_natCast_sub_nonneg_cube_le
    (n : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    |(n : ℝ) - μ| ^ 3 ≤ 4 * ((n : ℝ) ^ 3 + μ ^ 3) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have habs : |(n : ℝ) - μ| ≤ (n : ℝ) + μ := by
    calc
      |(n : ℝ) - μ| ≤ |(n : ℝ)| + |μ| := abs_sub _ _
      _ = (n : ℝ) + μ := by rw [abs_of_nonneg hn, abs_of_nonneg hμ]
  have hcube : |(n : ℝ) - μ| ^ 3 ≤ ((n : ℝ) + μ) ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg _) habs 3
  have hfactor : 0 ≤ 3 * ((n : ℝ) + μ) * ((n : ℝ) - μ) ^ 2 := by
    positivity
  calc
    |(n : ℝ) - μ| ^ 3 ≤ ((n : ℝ) + μ) ^ 3 := hcube
    _ ≤ 4 * ((n : ℝ) ^ 3 + μ ^ 3) := by nlinarith

/-- The third absolute centered moment of a geometric law is summable. -/
theorem summable_saddleGeometricWeight_mul_abs_centered_cube
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun n : ℕ => saddleGeometricWeight a n *
      |(n : ℝ) - saddleGeometricMean a| ^ 3) := by
  have hweight0 (n : ℕ) : 0 ≤ saddleGeometricWeight a n := by
    exact mul_nonneg (sub_nonneg.mpr ha1.le) (pow_nonneg ha0 n)
  have hμ0 : 0 ≤ saddleGeometricMean a := by
    exact div_nonneg ha0 (sub_nonneg.mpr ha1.le)
  let μ := saddleGeometricMean a
  have hthird := hasSum_saddleGeometricWeight_mul_natCast_cube ha0 ha1
  have hmass := (hasSum_saddleGeometricWeight ha0 ha1).mul_left (μ ^ 3)
  have hdom : Summable (fun n : ℕ => 4 *
      (saddleGeometricWeight a n * (n : ℝ) ^ 3 +
        μ ^ 3 * saddleGeometricWeight a n)) := by
    exact ((hthird.add hmass).mul_left 4).summable.congr (fun n => by ring)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (hweight0 n) (pow_nonneg (abs_nonneg _) 3))
    (fun n => by
      have h := mul_le_mul_of_nonneg_left
        (abs_natCast_sub_nonneg_cube_le n hμ0) (hweight0 n)
      nlinarith)
    hdom

/-- Uniform third absolute centered moment for all geometric ratios at most
`4/5`.  The deliberately round constant keeps later asymptotic estimates
transparent. -/
theorem tsum_saddleGeometricWeight_mul_abs_centered_cube_le
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 4 / 5) :
    (∑' n : ℕ, saddleGeometricWeight a n *
      |(n : ℝ) - saddleGeometricMean a| ^ 3) ≤ 4000 * a := by
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hweight0 (n : ℕ) : 0 ≤ saddleGeometricWeight a n := by
    exact mul_nonneg (sub_nonneg.mpr ha1.le) (pow_nonneg ha0 n)
  have hμ0 : 0 ≤ saddleGeometricMean a := by
    exact div_nonneg ha0 (sub_nonneg.mpr ha1.le)
  let μ := saddleGeometricMean a
  let D : ℝ := 4 *
    (a * (1 + 4 * a + a ^ 2) / (1 - a) ^ 3 + μ ^ 3)
  have hthird := hasSum_saddleGeometricWeight_mul_natCast_cube ha0 ha1
  have hmass := (hasSum_saddleGeometricWeight ha0 ha1).mul_left (μ ^ 3)
  have hdom : HasSum (fun n : ℕ => 4 *
      (saddleGeometricWeight a n * (n : ℝ) ^ 3 +
        μ ^ 3 * saddleGeometricWeight a n)) D := by
    dsimp only [D]
    convert (hthird.add hmass).mul_left 4 using 1
    all_goals ring
  have hpoint (n : ℕ) :
      saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3 ≤
        4 * (saddleGeometricWeight a n * (n : ℝ) ^ 3 +
          μ ^ 3 * saddleGeometricWeight a n) := by
    have h := mul_le_mul_of_nonneg_left
      (abs_natCast_sub_nonneg_cube_le n hμ0) (hweight0 n)
    nlinarith
  have hsummable : Summable (fun n : ℕ =>
      saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3) := by
    exact summable_saddleGeometricWeight_mul_abs_centered_cube ha0 ha1
  have htsum : (∑' n : ℕ,
      saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3) ≤ D := by
    exact (hsummable.tsum_le_tsum hpoint hdom.summable).trans_eq hdom.tsum_eq
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  have hdenLower : (1 / 5 : ℝ) ≤ 1 - a := by linarith
  have hdenCube : (1 / 125 : ℝ) ≤ (1 - a) ^ 3 := by
    calc
      (1 / 125 : ℝ) = (1 / 5 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - a) ^ 3 := by gcongr
  have haSq : a ^ 2 ≤ a := by nlinarith
  have hpoly : 1 + 4 * a + 2 * a ^ 2 ≤ 7 := by nlinarith
  have hD : D ≤ 4000 * a := by
    by_cases haZero : a = 0
    · subst a
      norm_num [D, μ, saddleGeometricMean]
    · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
      dsimp only [D, μ, saddleGeometricMean]
      rw [div_pow]
      have hform :
          4 * (a * (1 + 4 * a + a ^ 2) / (1 - a) ^ 3 +
              a ^ 3 / (1 - a) ^ 3) =
            4 * a * (1 + 4 * a + 2 * a ^ 2) / (1 - a) ^ 3 := by
        ring
      rw [hform]
      rw [div_le_iff₀ (pow_pos hden 3)]
      have hcore : 4 * (1 + 4 * a + 2 * a ^ 2) ≤
          4000 * (1 - a) ^ 3 := by
        calc
          4 * (1 + 4 * a + 2 * a ^ 2) ≤ 4 * 7 := by gcongr
          _ ≤ 4000 * (1 - a) ^ 3 := by nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hcore ha0
      nlinarith
  exact htsum.trans hD

/-- Third-order remainder for the pure-imaginary exponential on the unit
interval.  The quadratic polynomial is written in the form used after
centering a characteristic function. -/
theorem norm_exp_ofReal_mul_I_sub_quadratic_le_abs_cube
    {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ ≤
      |x| ^ 3 := by
  let z : ℂ := Complex.exp ((x : ℂ) * Complex.I) -
    (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)
  have hre : z.re = Real.cos x - (1 - x ^ 2 / 2) := by
    dsimp only [z]
    simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  have him : z.im = Real.sin x - x := by
    dsimp only [z]
    simp only [Complex.sub_im, Complex.exp_ofReal_mul_I_im,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, Complex.I_re]
    ring
  have hcos := Real.cos_bound hx
  have hsin := Real.sin_bound hx
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hpow : |x| ^ 4 ≤ |x| ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr hx)]
  have himBound : |Real.sin x - x| ≤ |x| ^ 3 * (7 / 32 : ℝ) := by
    calc
      |Real.sin x - x| =
          |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by ring_nf
      _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| :=
        abs_sub _ _
      _ ≤ |x| ^ 4 * (5 / 96 : ℝ) + |x| ^ 3 / 6 := by
        gcongr
        rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      _ ≤ |x| ^ 3 * (7 / 32 : ℝ) := by nlinarith
  calc
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ = ‖z‖ := rfl
    _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ = |Real.cos x - (1 - x ^ 2 / 2)| + |Real.sin x - x| := by
      rw [hre, him]
    _ ≤ |x| ^ 4 * (5 / 96 : ℝ) + |x| ^ 3 * (7 / 32 : ℝ) :=
      add_le_add hcos himBound
    _ ≤ |x| ^ 3 * (5 / 96 : ℝ) + |x| ^ 3 * (7 / 32 : ℝ) := by
      gcongr
    _ ≤ |x| ^ 3 := by
      have hcube : 0 ≤ |x| ^ 3 := pow_nonneg hx0 3
      nlinarith

/-- Global cubic remainder for a pure-imaginary exponential.  Outside the
unit interval the cubic majorant absorbs the elementary bound on the
exponential and its quadratic Taylor polynomial. -/
theorem norm_exp_ofReal_mul_I_sub_quadratic_le_four_mul_abs_cube
    (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ ≤
      4 * |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · exact (norm_exp_ofReal_mul_I_sub_quadratic_le_abs_cube hx).trans
      (by nlinarith [pow_nonneg (abs_nonneg x) 3])
  · have hxOne : 1 ≤ |x| := le_of_not_ge hx
    have hx0 : 0 ≤ |x| := abs_nonneg x
    have hreal : |1 - x ^ 2 / 2| ≤ 1 + |x| ^ 2 / 2 := by
      calc
        |1 - x ^ 2 / 2| ≤ |(1 : ℝ)| + |x ^ 2 / 2| := abs_sub _ _
        _ = 1 + |x| ^ 2 / 2 := by
          rw [abs_one, abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ ≤
          ‖Complex.exp ((x : ℂ) * Complex.I)‖ +
            ‖((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I‖ :=
        norm_sub_le _ _
      _ ≤ 1 +
          (‖((1 - x ^ 2 / 2 : ℝ) : ℂ)‖ + ‖(x : ℂ) * Complex.I‖) := by
        rw [Complex.norm_exp_ofReal_mul_I]
        gcongr
        exact norm_add_le _ _
      _ = 1 + (|1 - x ^ 2 / 2| + |x|) := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      _ ≤ 1 + (1 + |x| ^ 2 / 2 + |x|) := by gcongr
      _ ≤ 4 * |x| ^ 3 := by
        nlinarith [sq_nonneg (|x| - 1),
          mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hxOne)]

/-- Centered characteristic function of the geometric prime-power exponent. -/
noncomputable def saddleGeometricCenteredCharacteristic
    (a u : ℝ) : ℂ :=
  ∑' n : ℕ, ((saddleGeometricWeight a n : ℝ) : ℂ) *
    Complex.exp (((u * ((n : ℝ) - saddleGeometricMean a) : ℝ) : ℂ) *
      Complex.I)

/-- Closed form of the centered geometric characteristic function. -/
theorem saddleGeometricCenteredCharacteristic_eq_div
    {a u : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    saddleGeometricCenteredCharacteristic a u =
      Complex.exp (((-(u * saddleGeometricMean a) : ℝ) : ℂ) * Complex.I) *
        (((1 - a : ℝ) : ℂ) /
          (1 - (a : ℂ) * Complex.exp ((u : ℂ) * Complex.I))) := by
  let r : ℂ := (a : ℂ) * Complex.exp ((u : ℂ) * Complex.I)
  have hrnorm : ‖r‖ = a := by
    dsimp only [r]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hr : ‖r‖ < 1 := hrnorm.trans_lt ha1
  have hgeom := hasSum_geom_series_inverse r hr
  have hsum : HasSum (fun n : ℕ =>
      ((saddleGeometricWeight a n : ℝ) : ℂ) *
        Complex.exp (((u * ((n : ℝ) - saddleGeometricMean a) : ℝ) : ℂ) *
          Complex.I))
      (Complex.exp (((-(u * saddleGeometricMean a) : ℝ) : ℂ) * Complex.I) *
        (((1 - a : ℝ) : ℂ) * (1 - r)⁻¹)) := by
    convert hgeom.mul_left
      (Complex.exp (((-(u * saddleGeometricMean a) : ℝ) : ℂ) * Complex.I) *
        ((1 - a : ℝ) : ℂ)) using 1
    · ext n
      dsimp only [r, saddleGeometricWeight]
      rw [mul_pow, ← Complex.exp_nat_mul]
      have hexp :
          Complex.exp (((u * ((n : ℝ) - saddleGeometricMean a) : ℝ) : ℂ) *
            Complex.I) =
            Complex.exp (((-(u * saddleGeometricMean a) : ℝ) : ℂ) * Complex.I) *
              Complex.exp ((n : ℂ) * ((u : ℂ) * Complex.I)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      push_cast
      ring
    · simp only [Ring.inverse_eq_inv, mul_assoc]
  rw [saddleGeometricCenteredCharacteristic, hsum.tsum_eq]
  dsimp only [r]
  rw [div_eq_mul_inv]

/-- The mean of the geometric prime-power exponent, multiplied by `log p`,
is the corresponding first saddle summand. -/
theorem rpow_neg_mul_log_div_one_sub_eq_primeTerm
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) :
    (p : ℝ) ^ (-sigma) * Real.log (p : ℝ) /
        (1 - (p : ℝ) ^ (-sigma)) =
      smoothSaddlePrimeTerm p sigma := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hpowPos : 0 < (p : ℝ) ^ sigma := Real.rpow_pos_of_pos hpPos _
  have hdenPos : 0 < (p : ℝ) ^ sigma - 1 :=
    smoothSaddle_denominator_pos (by omega) hsigma
  rw [Real.rpow_neg hpPos.le]
  unfold smoothSaddlePrimeTerm
  field_simp [hpowPos.ne', hdenPos.ne']

/-- A centered geometric factor is exactly the centered prime-local Euler
factor once its phase is expressed in logarithmic frequency. -/
theorem saddleGeometricCenteredCharacteristic_eq_centeredPrimeFactor
    {p : ℕ} (hp : 1 < p) {sigma : ℝ} (hsigma : 0 < sigma) (t : ℝ) :
    saddleGeometricCenteredCharacteristic ((p : ℝ) ^ (-sigma))
        (t * Real.log (p : ℝ)) =
      Complex.exp
          ((-(t * smoothSaddlePrimeTerm p sigma) : ℝ) * Complex.I) *
        smoothTiltedPrimeCharacteristic p sigma t := by
  let a : ℝ := (p : ℝ) ^ (-sigma)
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have ha0 : 0 ≤ a := Real.rpow_nonneg hpPos.le _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp) (neg_neg_of_pos hsigma)
  have hmean :
      (t * Real.log (p : ℝ)) * saddleGeometricMean a =
        t * smoothSaddlePrimeTerm p sigma := by
    dsimp only [a, saddleGeometricMean]
    calc
      t * Real.log (p : ℝ) *
          ((p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma))) =
          t * ((p : ℝ) ^ (-sigma) * Real.log (p : ℝ) /
            (1 - (p : ℝ) ^ (-sigma))) := by ring
      _ = t * smoothSaddlePrimeTerm p sigma := by
        rw [rpow_neg_mul_log_div_one_sub_eq_primeTerm hp hsigma]
  rw [saddleGeometricCenteredCharacteristic_eq_div ha0 ha1, hmean]
  unfold smoothTiltedPrimeCharacteristic smoothFourierPrimeRatio
    smoothFourierWeight
  dsimp only [a]

/-- The centered geometric characteristic factor has its expected quadratic
expansion, with a uniform cubic error for ratios at most `4/5`. -/
theorem norm_saddleGeometricCenteredCharacteristic_sub_quadratic_le
    {a u : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 4 / 5) :
    ‖saddleGeometricCenteredCharacteristic a u -
        ((1 - u ^ 2 / 2 * (a / (1 - a) ^ 2) : ℝ) : ℂ)‖ ≤
      16000 * |u| ^ 3 * a := by
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  let μ := saddleGeometricMean a
  let v := a / (1 - a) ^ 2
  let F : ℕ → ℂ := fun n => ((saddleGeometricWeight a n : ℝ) : ℂ) *
    Complex.exp (((u * ((n : ℝ) - μ) : ℝ) : ℂ) * Complex.I)
  let P : ℕ → ℂ := fun n => ((saddleGeometricWeight a n : ℝ) : ℂ) *
    ((((1 - (u * ((n : ℝ) - μ)) ^ 2 / 2 : ℝ) : ℂ) +
      ((u * ((n : ℝ) - μ) : ℝ) : ℂ) * Complex.I))
  have hmass := hasSum_saddleGeometricWeight ha0 ha1
  have hcenter := hasSum_saddleGeometricWeight_mul_centered ha0 ha1
  have hvariance := hasSum_saddleGeometricWeight_mul_centered_sq ha0 ha1
  have hmassC := Complex.ofRealCLM.hasSum hmass
  have hcenterC := Complex.ofRealCLM.hasSum hcenter
  have hvarianceC := Complex.ofRealCLM.hasSum hvariance
  have hP : HasSum P (((1 - u ^ 2 / 2 * v : ℝ) : ℂ)) := by
    have hraw := (hmassC.sub
      (hvarianceC.mul_left (((u ^ 2 / 2 : ℝ) : ℂ)))).add
      (hcenterC.mul_left (((u : ℝ) : ℂ) * Complex.I))
    convert hraw using 1
    · ext n
      dsimp only [P, μ]
      simp only [Complex.ofRealCLM_apply]
      push_cast
      ring
    · dsimp only [v]
      simp only [Complex.ofRealCLM_apply]
      push_cast
      ring
  have hF : Summable F := by
    apply Summable.of_norm
    exact hmass.summable.congr (fun n => by
      have hw : 0 ≤ saddleGeometricWeight a n :=
        mul_nonneg (sub_nonneg.mpr ha1.le) (pow_nonneg ha0 n)
      symm
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hw])
  have herror : HasSum (fun n => F n - P n)
      (saddleGeometricCenteredCharacteristic a u -
        ((1 - u ^ 2 / 2 * v : ℝ) : ℂ)) := by
    have := hF.hasSum.sub hP
    simpa only [saddleGeometricCenteredCharacteristic, F, μ] using this
  have habsMoment :=
    summable_saddleGeometricWeight_mul_abs_centered_cube ha0 ha1
  have hmajorant : Summable (fun n : ℕ =>
      (4 * |u| ^ 3) *
        (saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3)) :=
    habsMoment.mul_left (4 * |u| ^ 3)
  have hpoint (n : ℕ) : ‖F n - P n‖ ≤
      (4 * |u| ^ 3) *
        (saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3) := by
    have hw0 : 0 ≤ saddleGeometricWeight a n :=
      mul_nonneg (sub_nonneg.mpr ha1.le) (pow_nonneg ha0 n)
    let x : ℝ := u * ((n : ℝ) - μ)
    have hlocal := norm_exp_ofReal_mul_I_sub_quadratic_le_four_mul_abs_cube x
    have heq : F n - P n =
        ((saddleGeometricWeight a n : ℝ) : ℂ) *
          (Complex.exp ((x : ℂ) * Complex.I) -
            (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)) := by
      dsimp only [F, P, x]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw0]
    calc
      saddleGeometricWeight a n *
          ‖Complex.exp ((x : ℂ) * Complex.I) -
            (((1 - x ^ 2 / 2 : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ ≤
          saddleGeometricWeight a n * (4 * |x| ^ 3) :=
        mul_le_mul_of_nonneg_left hlocal hw0
      _ = (4 * |u| ^ 3) *
          (saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3) := by
        dsimp only [x]
        rw [abs_mul, mul_pow]
        ring
  rw [← herror.tsum_eq]
  calc
    ‖∑' n : ℕ, (F n - P n)‖ ≤ ∑' n : ℕ, ‖F n - P n‖ :=
      norm_tsum_le_tsum_norm herror.summable.norm
    _ ≤ ∑' n : ℕ, (4 * |u| ^ 3) *
          (saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3) :=
      herror.summable.norm.tsum_le_tsum hpoint hmajorant
    _ = (4 * |u| ^ 3) * (∑' n : ℕ,
          saddleGeometricWeight a n * |(n : ℝ) - μ| ^ 3) := by
      rw [tsum_mul_left]
    _ ≤ (4 * |u| ^ 3) * (4000 * a) := by
      gcongr
      exact tsum_saddleGeometricWeight_mul_abs_centered_cube_le ha0 ha
    _ = 16000 * |u| ^ 3 * a := by ring

/-- Prime-local Taylor bound at the exact saddle, before summing over the
source primes. -/
theorem norm_smoothSaddleCenteredPrimeCharacteristic_sub_quadratic_le
    {X y p : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hp : p ∈ (Finset.Icc 2 y).filter Nat.Prime) (t : ℝ)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) :
    ‖smoothSaddleCenteredPrimeCharacteristic X y p t -
        ((1 - (t ^ 2 / 2) *
          smoothSaddlePrimeVarianceShare X y p : ℝ) : ℂ)‖ ≤
      16000 *
        |(t / smoothSaddleStandardDeviation X y) * Real.log (p : ℝ)| ^ 3 *
          (p : ℝ) ^ (-smoothSaddlePoint X y) := by
  let sigma := smoothSaddlePoint X y
  let sd := smoothSaddleStandardDeviation X y
  let a : ℝ := (p : ℝ) ^ (-sigma)
  let u : ℝ := (t / sd) * Real.log (p : ℝ)
  have hpTwo : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hpOne : 1 < p := by omega
  have hsigmaPos : 0 < sigma := by
    exact smoothSaddlePoint_pos hX hy
  have hsdPos : 0 < sd := smoothSaddleStandardDeviation_pos hX hy
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  have ha : a ≤ 4 / 5 := by
    have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hs0 := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    have hinvSqrt : (Real.sqrt 2)⁻¹ ≤ (4 / 5 : ℝ) := by
      rw [inv_le_comm₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
        (by norm_num : (0 : ℝ) < 4 / 5)]
      norm_num
      exact hsqrt
    have haHalf : a ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ p by omega) : (1 : ℝ) ≤ p)
        (neg_le_neg (by simpa only [sigma] using hsigma))
    have hpHalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hpTwo)
        (by norm_num)
    have htwoHalf : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (4 / 5 : ℝ) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
      exact hinvSqrt
    exact haHalf.trans (hpHalf.trans htwoHalf)
  have hfactor :
      smoothSaddleCenteredPrimeCharacteristic X y p t =
        saddleGeometricCenteredCharacteristic a u := by
    rw [saddleGeometricCenteredCharacteristic_eq_centeredPrimeFactor
      hpOne hsigmaPos (t / sd)]
    unfold smoothSaddleCenteredPrimeCharacteristic
    dsimp only [sigma, sd, a, u]
    congr 2
    congr 2
    ring
  have hsdSq : sd ^ 2 = smoothSaddlePhiTwo y sigma := by
    dsimp only [sd, sigma, smoothSaddleStandardDeviation]
    exact Real.sq_sqrt
      (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)).le
  have hquad :
      u ^ 2 / 2 * (a / (1 - a) ^ 2) =
        (t ^ 2 / 2) * smoothSaddlePrimeVarianceShare X y p := by
    have hsecond : a * Real.log (p : ℝ) ^ 2 / (1 - a) ^ 2 =
        smoothSaddleSecondPrimeTerm p sigma := by
      dsimp only [a]
      exact rpow_neg_mul_log_sq_div_one_sub_sq_eq_secondPrimeTerm
        hpOne hsigmaPos
    unfold smoothSaddlePrimeVarianceShare
    change u ^ 2 / 2 * (a / (1 - a) ^ 2) =
      t ^ 2 / 2 * (smoothSaddleSecondPrimeTerm p sigma /
        smoothSaddlePhiTwo y sigma)
    rw [← hsecond, ← hsdSq]
    dsimp only [u]
    field_simp [hsdPos.ne']
  rw [hfactor, ← hquad]
  exact norm_saddleGeometricCenteredCharacteristic_sub_quadratic_le ha0 ha

/-- Summing the prime-local Taylor errors costs only the largest normalized
prime logarithm. -/
theorem sum_norm_smoothSaddleCenteredPrimeCharacteristic_sub_quadratic_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) :
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
      ‖smoothSaddleCenteredPrimeCharacteristic X y p t -
        ((1 - (t ^ 2 / 2) *
          smoothSaddlePrimeVarianceShare X y p : ℝ) : ℂ)‖) ≤
      16000 * |t| ^ 3 *
        (Real.log (y : ℝ) / smoothSaddleStandardDeviation X y) := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  let sigma := smoothSaddlePoint X y
  let sd := smoothSaddleStandardDeviation X y
  let C : ℝ := 16000 * |t| ^ 3 / sd ^ 3
  have hsdPos : 0 < sd := smoothSaddleStandardDeviation_pos hX hy
  have hC0 : 0 ≤ C := by positivity
  have hlogy0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hsdSq : sd ^ 2 = smoothSaddlePhiTwo y sigma := by
    dsimp only [sd, sigma, smoothSaddleStandardDeviation]
    exact Real.sq_sqrt
      (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)).le
  have hterm (p : ℕ) (hp : p ∈ S) :
      ‖smoothSaddleCenteredPrimeCharacteristic X y p t -
          ((1 - (t ^ 2 / 2) *
            smoothSaddlePrimeVarianceShare X y p : ℝ) : ℂ)‖ ≤
        C * ((p : ℝ) ^ (-sigma) * Real.log (p : ℝ) ^ 3) := by
    have hlocal :=
      norm_smoothSaddleCenteredPrimeCharacteristic_sub_quadratic_le
        hX hy hp t hsigma
    have hpTwo : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    calc
      ‖smoothSaddleCenteredPrimeCharacteristic X y p t -
          ((1 - (t ^ 2 / 2) *
            smoothSaddlePrimeVarianceShare X y p : ℝ) : ℂ)‖ ≤
          16000 * |(t / sd) * Real.log (p : ℝ)| ^ 3 *
            (p : ℝ) ^ (-sigma) := by
              simpa only [sd, sigma] using hlocal
      _ = C * ((p : ℝ) ^ (-sigma) * Real.log (p : ℝ) ^ 3) := by
        dsimp only [C]
        rw [abs_mul, abs_div, abs_of_pos hsdPos, abs_of_nonneg hlogp0,
          ]
        field_simp [hsdPos.ne']
  have hprime (p : ℕ) (hp : p ∈ S) :
      (p : ℝ) ^ (-sigma) * Real.log (p : ℝ) ^ 3 ≤
        Real.log (y : ℝ) * smoothSaddleSecondPrimeTerm p sigma := by
    have hpIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have hpOne : 1 < p := by omega
    have hpPos : (0 : ℝ) < p := by positivity
    have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hlogpy : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (p : ℝ) ∈ Set.Ioi 0 from hpPos)
        (show (y : ℝ) ∈ Set.Ioi 0 from
          (by exact_mod_cast (show 0 < y by omega) : (0 : ℝ) < y))
        (by exact_mod_cast hpIcc.2)
    let a : ℝ := (p : ℝ) ^ (-sigma)
    have ha0 : 0 ≤ a := Real.rpow_nonneg hpPos.le _
    have haLt : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hpOne) (neg_neg_of_pos (smoothSaddlePoint_pos hX hy))
    have hdenPos : 0 < 1 - a := sub_pos.mpr haLt
    have hdenSq : (1 - a) ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    have hbase : a * Real.log (p : ℝ) ^ 2 ≤
        smoothSaddleSecondPrimeTerm p sigma := by
      rw [← rpow_neg_mul_log_sq_div_one_sub_sq_eq_secondPrimeTerm
        hpOne (smoothSaddlePoint_pos hX hy)]
      dsimp only [a]
      rw [le_div_iff₀ (sq_pos_of_pos hdenPos)]
      nlinarith [mul_nonneg ha0 (sq_nonneg (Real.log (p : ℝ)))]
    calc
      (p : ℝ) ^ (-sigma) * Real.log (p : ℝ) ^ 3 =
          Real.log (p : ℝ) *
            ((p : ℝ) ^ (-sigma) * Real.log (p : ℝ) ^ 2) := by ring
      _ ≤ Real.log (y : ℝ) * smoothSaddleSecondPrimeTerm p sigma :=
        mul_le_mul hlogpy hbase
          (mul_nonneg ha0 (sq_nonneg (Real.log (p : ℝ)))) hlogy0
  calc
    (∑ p ∈ S,
      ‖smoothSaddleCenteredPrimeCharacteristic X y p t -
        ((1 - (t ^ 2 / 2) *
          smoothSaddlePrimeVarianceShare X y p : ℝ) : ℂ)‖) ≤
        ∑ p ∈ S, C *
          ((p : ℝ) ^ (-sigma) * Real.log (p : ℝ) ^ 3) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ ≤ ∑ p ∈ S,
        C * (Real.log (y : ℝ) * smoothSaddleSecondPrimeTerm p sigma) := by
      exact Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hprime p hp) hC0
    _ = C * (Real.log (y : ℝ) * smoothSaddlePhiTwo y sigma) := by
      simp only [← Finset.mul_sum]
      rfl
    _ = 16000 * |t| ^ 3 * (Real.log (y : ℝ) / sd) := by
      dsimp only [C]
      rw [← hsdSq]
      field_simp [hsdPos.ne']

/-- In the critical smooth regime, the summed prime-local cubic Taylor error
tends to zero at every fixed normalized frequency. -/
theorem IsTaoCriticalSmoothRegime.tendsto_primeLocalTaylorError_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) (t : ℝ) :
    Tendsto (fun n =>
      ∑ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        ‖smoothSaddleCenteredPrimeCharacteristic (X n) (y n) p t -
          ((1 - (t ^ 2 / 2) *
            smoothSaddlePrimeVarianceShare (X n) (y n) p : ℝ) : ℂ)‖)
      atTop (nhds 0) := by
  have hsigma : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ smoothSaddlePoint (X n) (y n) :=
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hupper : ∀ᶠ n in atTop,
      (∑ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        ‖smoothSaddleCenteredPrimeCharacteristic (X n) (y n) p t -
          ((1 - (t ^ 2 / 2) *
            smoothSaddlePrimeVarianceShare (X n) (y n) p : ℝ) : ℂ)‖) ≤
        16000 * |t| ^ 3 *
          (Real.log (y n : ℝ) /
            smoothSaddleStandardDeviation (X n) (y n)) := by
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα, hsigma] with n hX hy hs
    exact sum_norm_smoothSaddleCenteredPrimeCharacteristic_sub_quadratic_le
      hX hy t hs
  have htend : Tendsto (fun n =>
      16000 * |t| ^ 3 *
        (Real.log (y n : ℝ) /
          smoothSaddleStandardDeviation (X n) (y n)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (hregime.tendsto_log_y_div_saddleStandardDeviation_zero hα)
  exact squeeze_zero'
    (Eventually.of_forall fun n => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    hupper htend

/-- Unconditional fixed-frequency Gaussian convergence of the exact
variance-normalized saddle characteristic function in the critical regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_normalizedCharacteristic_gaussian
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleNormalizedCharacteristic (X n) (y n) t)
      atTop (nhds (Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))) := by
  exact hregime.tendsto_normalizedCharacteristic_gaussian_of_primeLocalError
    hα (hregime.tendsto_primeLocalTaylorError_zero hα t)

end

end Tao2026
