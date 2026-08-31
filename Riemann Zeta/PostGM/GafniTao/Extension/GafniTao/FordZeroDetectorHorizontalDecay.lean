import GafniTao.FordZeroDetectorFiniteEdges
import GafniTao.SharpPerronHorizontalAll

/-!
# Horizontal decay in Ford's zero detector

The finite residue identity cannot be sent to infinite height using the
cotangent kernel itself: the cotangent approaches a nonzero imaginary
constant.  Ford first integrates by parts.  The derivative of the kernel is
quadratically reciprocal to a complex sine and therefore decays
exponentially on the horizontal edges.  This file proves that exact analytic
fact, independently of the later logarithm-branch construction.
-/

open Complex Set

namespace GafniTao

noncomputable section

theorem norm_sin_add_mul_I_sq (x y : ℝ) :
    ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 =
      Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.sin_add_mul_I, Complex.normSq_apply,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq x,
    Real.cosh_sq_sub_sinh_sq y]

theorem abs_sinh_le_norm_sin_add_mul_I (x y : ℝ) :
    |Real.sinh y| ≤
      ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _),
    norm_sin_add_mul_I_sq, sq_abs]
  nlinarith [sq_nonneg (Real.sin x)]

theorem exp_div_four_le_sinh {y : ℝ} (hy : 1 ≤ y) :
    Real.exp y / 4 ≤ Real.sinh y := by
  have hexpTwo : 2 ≤ Real.exp y := by
    exact (calc
      (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      _ ≤ Real.exp y := Real.exp_le_exp.mpr hy).le
  have hexpNeg : Real.exp (-y) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  rw [Real.sinh_eq]
  nlinarith

theorem exp_div_four_le_norm_sin_add_mul_I
    (x : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    Real.exp y / 4 ≤
      ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  exact (exp_div_four_le_sinh hy).trans
    ((le_abs_self _).trans (abs_sinh_le_norm_sin_add_mul_I x y))

/-- The exact exponential majorant for the derivative of Ford's cotangent
kernel on an upper horizontal edge.  This is the decay mechanism used after
integration by parts in Ford's zero detector. -/
theorem norm_deriv_fordCotKernel_horizontal_le
    {eta R x : ℝ} (heta : 0 < eta)
    (hheight : 1 ≤ (Real.pi / (2 * eta)) * R) :
    ‖deriv (fordCotKernel eta)
        ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤
      16 * (Real.pi / (2 * eta)) ^ 2 *
        Real.exp (-2 * ((Real.pi / (2 * eta)) * R)) := by
  let c : ℝ := Real.pi / (2 * eta)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hscale :
      ((c : ℂ) * ((x : ℂ) + (R : ℂ) * Complex.I)) =
        ((c * x : ℝ) : ℂ) + ((c * R : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hsinLower : Real.exp (c * R) / 4 ≤
      ‖Complex.sin
        (((Real.pi / (2 * eta) : ℝ) : ℂ) *
          ((x : ℂ) + (R : ℂ) * Complex.I))‖ := by
    rw [show (Real.pi / (2 * eta) : ℝ) = c by rfl, hscale]
    exact exp_div_four_le_norm_sin_add_mul_I (c * x) hheight
  have hsinPos : 0 <
      ‖Complex.sin
        (((Real.pi / (2 * eta) : ℝ) : ℂ) *
          ((x : ℂ) + (R : ℂ) * Complex.I))‖ :=
    (div_pos (Real.exp_pos _) (by norm_num)).trans_le hsinLower
  have hsinNe : Complex.sin
      (((Real.pi / (2 * eta) : ℝ) : ℂ) *
        ((x : ℂ) + (R : ℂ) * Complex.I)) ≠ 0 :=
    norm_pos_iff.mp hsinPos
  rw [(hasDerivAt_fordCotKernel hsinNe).deriv, norm_div, norm_neg,
    norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos hc, show Real.pi / (2 * eta) = c by rfl]
  have hdenSq : (Real.exp (c * R) / 4) ^ 2 ≤
      ‖Complex.sin
        ((c : ℂ) * ((x : ℂ) + (R : ℂ) * Complex.I))‖ ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hsinLower
  have hdenSqPos : 0 <
      ‖Complex.sin
        ((c : ℂ) * ((x : ℂ) + (R : ℂ) * Complex.I))‖ ^ 2 :=
    sq_pos_of_pos hsinPos
  rw [norm_pow, div_le_iff₀ hdenSqPos]
  have hexpId : Real.exp (-2 * (c * R)) * Real.exp (c * R) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hfactor :
      16 * Real.exp (-2 * (c * R)) * (Real.exp (c * R) / 4) ^ 2 = 1 := by
    rw [div_pow]
    calc
      16 * Real.exp (-2 * (c * R)) * (Real.exp (c * R) ^ 2 / 4 ^ 2) =
          Real.exp (-2 * (c * R)) * Real.exp (c * R) ^ 2 := by ring
      _ = 1 := hexpId
  have heq :
      16 * c ^ 2 * Real.exp (-2 * (c * R)) *
          (Real.exp (c * R) / 4) ^ 2 = c ^ 2 := by
    calc
      _ = c ^ 2 *
          (16 * Real.exp (-2 * (c * R)) *
            (Real.exp (c * R) / 4) ^ 2) := by ring
      _ = c ^ 2 := by rw [hfactor, mul_one]
  calc
    c ^ 2 ≤
        16 * c ^ 2 * Real.exp (-2 * (c * R)) *
          (Real.exp (c * R) / 4) ^ 2 := heq.ge
    _ ≤ 16 * c ^ 2 * Real.exp (-2 * (c * R)) *
          ‖Complex.sin
            ((c : ℂ) * ((x : ℂ) + (R : ℂ) * Complex.I))‖ ^ 2 := by
      gcongr

end

end GafniTao
