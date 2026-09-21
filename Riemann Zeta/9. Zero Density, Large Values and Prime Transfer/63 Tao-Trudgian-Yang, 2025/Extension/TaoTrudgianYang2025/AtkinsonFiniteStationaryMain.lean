import TaoTrudgianYang2025.AtkinsonStationaryReduction

/-!
# Exact finite stationary main term for the actual signed carrier

The quadratic integral is still a finite integral, not an assumed Fresnel
constant. Its central phase, curvature and square-root normalization are
proved from the same saddle that occurs in the source integral.
-/

noncomputable section

open Complex MeasureTheory Set

namespace TaoTrudgianYang2025

def atkinsonSaddleCurvature (T b : ℝ) : ℝ :=
  1 + (T / (2 * Real.pi)) / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2

def atkinsonQuadraticWindow (c H : ℝ) : ℂ :=
  ∫ z in (-H)..H, Complex.exp (((-2 * Real.pi * c * z ^ 2 : ℝ) : ℂ) * I)

def atkinsonFiniteStationaryMain (T G L α b H : ℝ) : ℂ :=
  2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
    atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
      atkinsonQuadraticWindow (atkinsonSaddleCurvature T b) H

theorem one_lt_atkinsonSaddleCurvature {T : ℝ} (hT : 0 < T) (b : ℝ) :
    1 < atkinsonSaddleCurvature T b := by
  have hr := atkinsonSaddleRoot_pos (by positivity : 0 < T / (2 * Real.pi)) b
  unfold atkinsonSaddleCurvature
  have hp : 0 < (T / (2 * Real.pi)) / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2 := by
    positivity
  linarith

theorem atkinsonSaddleCurvature_mul_root {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonSaddleCurvature T b * atkinsonSaddleRoot (T / (2 * Real.pi)) b =
      Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi))) := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  let s := atkinsonSaddleRoot (T / (2 * Real.pi)) (-b)
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hprod : r * s = T / (2 * Real.pi) := atkinsonSaddleRoot_mul_neg (by positivity) b
  have hsum : r + s = Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi))) :=
    atkinsonSaddleRoot_sum_neg _ b
  change (1 + (T / (2 * Real.pi)) / r ^ 2) * r = _
  rw [← hsum, ← hprod]
  field_simp

theorem atkinsonSaddle_squareRoot_normalization {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Real.sqrt (atkinsonSaddleCurvature T b) *
      Real.sqrt (atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
        Real.sqrt (Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi)))) := by
  rw [← Real.sqrt_mul (by linarith [one_lt_atkinsonSaddleCurvature hT b]),
    atkinsonSaddleCurvature_mul_root hT b]

theorem atkinsonRootQuadraticKernel_translate (T b z : ℝ) :
    atkinsonRootQuadraticKernel T b (z + atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
      atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        Complex.exp (((-2 * Real.pi * atkinsonSaddleCurvature T b * z ^ 2 : ℝ) : ℂ) * I) := by
  unfold atkinsonRootQuadraticKernel atkinsonRootQuadratic atkinsonRootKernel atkinsonSaddleCurvature
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_atkinsonRootQuadraticKernel (T b H : ℝ) :
    (∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
      (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y) =
      atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        atkinsonQuadraticWindow (atkinsonSaddleCurvature T b) H := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hs := intervalIntegral.integral_comp_add_right (atkinsonRootQuadraticKernel T b) r
    (a := -H) (b := H)
  rw [show -H + r = r - H by ring, show H + r = r + H by ring] at hs
  change (∫ y in (r - H)..(r + H), atkinsonRootQuadraticKernel T b y) = _
  rw [← hs]
  simp_rw [show ∀ z, atkinsonRootQuadraticKernel T b (z + r) =
    atkinsonRootKernel T b r *
      Complex.exp (((-2 * Real.pi * atkinsonSaddleCurvature T b * z ^ 2 : ℝ) : ℂ) * I) from
        atkinsonRootQuadraticKernel_translate T b]
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem atkinsonFiniteStationaryMain_eq_quadratic (T G L α b H : ℝ) :
    atkinsonFiniteStationaryMain T G L α b H =
      2 * atkinsonPowerWeight T G L α ((atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2) *
        ∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
          (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y := by
  rw [integral_atkinsonRootQuadraticKernel]
  unfold atkinsonFiniteStationaryMain
  ring

theorem exists_atkinsonPowerIntegral_finite_stationary_approximation (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b H : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → 0 < H →
      Real.sqrt T / 4 ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b - H →
      atkinsonSaddleRoot (T / (2 * Real.pi)) b + H ≤ Real.sqrt T →
      H ≤ atkinsonSaddleRoot (T / (2 * Real.pi)) b / 2 →
      ‖atkinsonPowerIntegral T G L α b - atkinsonFiniteStationaryMain T G L α b H‖ ≤
        C * G * T ^ (-α) * (4 / (H * Real.pi) + 4 * (G / Real.sqrt T) * H ^ 2 +
          16 * T * H ^ 4 / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 3) := by
  simpa only [atkinsonFiniteStationaryMain_eq_quadratic] using
    exists_atkinsonPowerIntegral_quadratic_approximation α

end TaoTrudgianYang2025
