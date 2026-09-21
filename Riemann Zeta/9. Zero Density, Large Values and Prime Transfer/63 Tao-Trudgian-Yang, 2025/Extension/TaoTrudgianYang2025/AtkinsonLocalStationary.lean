import TaoTrudgianYang2025.AtkinsonNaturalAmplitude

/-!
# Actual local stationary integral reduced to a frozen quadratic integral

The remainder consumes the constructed amplitude derivatives and the cubic
error of the actual logarithmic phase. Window containment is geometric,
not a supplied stationary-phase estimate. Full Fresnel evaluation and the
complementary source-scale error remain separate obligations.
-/

noncomputable section

open Complex MeasureTheory Set

namespace TaoTrudgianYang2025

def atkinsonRootQuadraticKernel (T b y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * atkinsonRootQuadratic T b y : ℝ) : ℂ) * I)

theorem norm_atkinsonRootQuadraticKernel (T b y : ℝ) :
    ‖atkinsonRootQuadraticKernel T b y‖ = 1 := by
  simp [atkinsonRootQuadraticKernel, Complex.norm_exp]

theorem continuous_atkinsonRootQuadraticKernel (T b : ℝ) :
    Continuous (atkinsonRootQuadraticKernel T b) := by
  unfold atkinsonRootQuadraticKernel atkinsonRootQuadratic
  fun_prop

theorem IntervalC2Bound.atkinsonLocalQuadratic {f : ℝ → ℂ} {a c M R T H : ℝ}
    (hf : IntervalC2Bound f a c M R) (hT : 0 < T) (b : ℝ) (hH : 0 ≤ H)
    (hleft : a ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)
    (hright : atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ c)
    (hwindow : H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2) :
    ‖(∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), f y * atkinsonRootKernel T b y) -
      f (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
      M * (2 * R * H ^ 2 + 8 * T * H ^ 4 /
        (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have horder : r - H ≤ r + H := by linarith
  have hpositive : 0 < r - H := by change H ≤ r / 2 at hwindow; linarith
  have hmem {y : ℝ} (hy : y ∈ Icc (r - H) (r + H)) : y ∈ Icc a c :=
    ⟨hleft.trans hy.1, hy.2.trans hright⟩
  have hrmem : r ∈ Icc a c := hmem ⟨by linarith, by linarith⟩
  have hfcont : ContinuousOn f (uIcc (r - H) (r + H)) := by
    rw [uIcc_of_le horder]
    exact fun y hy => (hf.smooth y (hmem hy)).continuousAt.continuousWithinAt
  have hactual : IntervalIntegrable (fun y => f y * atkinsonRootKernel T b y)
      volume (r - H) (r + H) :=
    hfcont.intervalIntegrable.mul_continuousOn (by
      rw [uIcc_of_le horder]
      exact fun y hy => (continuousAt_atkinsonRootKernel T b
        (hpositive.trans_le hy.1)).continuousWithinAt)
  have hquad := (continuous_atkinsonRootQuadraticKernel T b).intervalIntegrable
    (μ := volume) (a := r - H) (b := r + H)
  have hpoint (y : ℝ) (hy : y ∈ Icc (r - H) (r + H)) :
      ‖f y * atkinsonRootKernel T b y - f r * atkinsonRootQuadraticKernel T b y‖ ≤
        M * R * H + M * (4 * T * H ^ 3 / r ^ 3) := by
    have hyH : |y - r| ≤ H := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hvar : ‖f y - f r‖ ≤ M * R * H :=
      (hf.norm_sub_le hrmem (hmem hy)).trans
        (mul_le_mul_of_nonneg_left hyH (mul_nonneg hf.nonneg hf.scale_nonneg))
    have hphase : ‖atkinsonRootKernel T b y - atkinsonRootQuadraticKernel T b y‖ ≤
        4 * T * H ^ 3 / r ^ 3 := by
      apply (norm_atkinsonRootKernel_sub_quadratic_le hT b (hyH.trans hwindow)).trans
      change 4 * T * |y - r| ^ 3 / r ^ 3 ≤ _
      gcongr
    have he : f y * atkinsonRootKernel T b y - f r * atkinsonRootQuadraticKernel T b y =
        (f y - f r) * atkinsonRootKernel T b y +
          f r * (atkinsonRootKernel T b y - atkinsonRootQuadraticKernel T b y) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_atkinsonRootKernel, mul_one, norm_mul]
    exact add_le_add hvar (mul_le_mul (hf.norm_le r hrmem) hphase (norm_nonneg _) hf.nonneg)
  change ‖(∫ y in (r - H)..(r + H), f y * atkinsonRootKernel T b y) -
    f r * ∫ y in (r - H)..(r + H), atkinsonRootQuadraticKernel T b y‖ ≤ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hactual
    (hquad.const_mul (f r))]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r - H) (b := r + H) (fun y hy => hpoint y (by
      rw [uIoc_of_le horder] at hy
      exact ⟨hy.1.le, hy.2⟩))
  apply hbound.trans_eq
  rw [abs_of_nonneg (by linarith : 0 ≤ r + H - (r - H))]
  ring

theorem exists_atkinsonPowerIntegral_local_quadratic_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 ≤ H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖2 * (∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H),
            atkinsonPowerWeight T G L α (y ^ 2) * atkinsonRootKernel T b y) -
        2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
          ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
            (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y‖ ≤
        C * G * T ^ (-α) * (4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨C, hC, ?_⟩
  intro T G L b H hT hG hGT hL hwidth hH hleft hright hwindow
  have h := (hbound T G L hT hG hGT hL hwidth).atkinsonLocalQuadratic
    hT b hH hleft hright hwindow
  have he (x y z : ℂ) : 2 * x - 2 * y * z = 2 * (x - y * z) := by ring
  rw [he, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  ring

end TaoTrudgianYang2025
