import TaoTrudgianYang2025.SecondDerivativeComposition

/-!
# Uniform second derivatives of the actual rescaled Gaussian profile

The fixed logarithmic profile has bounded derivatives on one compact
interval. Both chain-rule terms consume the true Gaussian derivative
bounds. All constants are chosen before the source height and width.
-/

noncomputable section

open Complex Filter Set Topology
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem norm_deriv_zetaGaussianQuadraticIntegral_le_polynomial {T G : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖deriv (zetaGaussianQuadraticIntegral T G) v‖ ≤
      (Real.sqrt Real.pi * G ^ 3 / 2) * |v| := by
  apply (norm_deriv_zetaGaussianQuadraticIntegral_le hT hG hGT v).trans
  have he : Real.exp (-(G * v) ^ 2 / 8) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (G * v)])
  have h := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (Real.sqrt Real.pi * G ^ 3 / 2) * |v| by positivity)
  simpa only [mul_one] using h

theorem quadraticGaussian_derivatives_of_bounded_argument {T G B v : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T)
    (hv : |v| ≤ B) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤ Real.sqrt Real.pi * G ∧
    ‖deriv (zetaGaussianQuadraticIntegral T G) v‖ ≤ B * Real.sqrt Real.pi * G * T ∧
    ‖iteratedDeriv 2 (zetaGaussianQuadraticIntegral T G) v‖ ≤
      (B ^ 2 + 1) * Real.sqrt Real.pi * G * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  refine ⟨norm_zetaGaussianQuadraticIntegral_le_mass hT0 hG hGT v, ?_, ?_⟩
  · apply (norm_deriv_zetaGaussianQuadraticIntegral_le_polynomial hT0 hG hGT v).trans
    have hp := mul_le_mul (show G ^ 2 / 2 ≤ T by linarith) hv (abs_nonneg _) hT0.le
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ Real.sqrt Real.pi * G by positivity)
    convert h using 1 <;> ring
  · have hv2 := pow_le_pow_left₀ (abs_nonneg v) hv 2
    rw [sq_abs] at hv2
    have hG4 : G ^ 4 ≤ 4 * T ^ 2 := by
      have h := pow_le_pow_left₀ (sq_nonneg G) hGT 2
      nlinarith
    have hp := mul_le_mul hv2 hG4 (by positivity : 0 ≤ G ^ 4) (sq_nonneg B)
    have hcoef : v ^ 2 * G ^ 4 / 4 + G ^ 2 / 2 ≤ (B ^ 2 + 1) * T ^ 2 := by
      nlinarith
    apply (norm_iteratedDeriv_two_zetaGaussianQuadraticIntegral_le_polynomial hT0 hG hGT v).trans
    calc
      _ ≤ ((B ^ 2 + 1) * T ^ 2) * (Real.sqrt Real.pi * G) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring

theorem exists_intervalC2Bound_quadraticGaussian_profile {v : ℝ → ℝ} {a b : ℝ}
    (hv : ∀ u ∈ Icc a b, ContDiffAt ℝ 2 v u) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      IntervalC2Bound (fun u => zetaGaussianQuadraticIntegral T G (v u)) a b (C * G) T := by
  obtain ⟨M, hM, hprofile⟩ := exists_real_profile_derivative_bound hv
  have hv0 (u : ℝ) (hu : u ∈ Icc a b) : |v u| ≤ M := (hprofile u hu).1
  have hv1 (u : ℝ) (hu : u ∈ Icc a b) : |deriv v u| ≤ M := (hprofile u hu).2.1
  have hv2 (u : ℝ) (hu : u ∈ Icc a b) : |iteratedDeriv 2 v u| ≤ M := (hprofile u hu).2.2
  let A : ℝ := 1 + 3 * M ^ 2 + M ^ 4
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg (M ^ 2)]
  have hAM : M ^ 2 ≤ A := by dsimp [A]; nlinarith [sq_nonneg (M ^ 2)]
  have hAM2 : M ^ 2 * (M ^ 2 + 1) + M ^ 2 ≤ A := by dsimp [A]; nlinarith
  refine ⟨Real.sqrt Real.pi * A, by positivity, ?_⟩
  intro T G hT hG hGT
  have hT0 : 0 < T := by linarith
  have hQ : ContDiff ℝ 2 (zetaGaussianQuadraticIntegral T G) :=
    (contDiff_zetaGaussianQuadraticIntegral T hG.ne').of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2)))
  have hb (u : ℝ) (hu : u ∈ Icc a b) :=
    quadraticGaussian_derivatives_of_bounded_argument hT hG hGT (hv0 u hu)
  refine ⟨by positivity, hT0.le, fun u hu => hQ.contDiffAt.comp u (hv u hu), ?_, ?_, ?_⟩
  · intro u hu
    apply (hb u hu).1.trans
    have h := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ Real.sqrt Real.pi * G by positivity)
    nlinarith
  · intro u hu
    have hd : HasDerivAt (fun w => zetaGaussianQuadraticIntegral T G (v w))
        (deriv v u • deriv (zetaGaussianQuadraticIntegral T G) (v u)) u :=
      (hQ.differentiable (by norm_num)).differentiableAt.hasDerivAt.scomp
        (h := v) u ((hv u hu).differentiableAt (by norm_num)).hasDerivAt
    rw [hd.deriv, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ M * (M * Real.sqrt Real.pi * G * T) :=
        mul_le_mul (hv1 u hu) (hb u hu).2.1 (norm_nonneg _) hM.le
      _ ≤ (Real.sqrt Real.pi * A * G) * T := by
        have h := mul_le_mul_of_nonneg_right hAM
          (show 0 ≤ Real.sqrt Real.pi * G * T by positivity)
        nlinarith
  · intro u hu
    rw [iteratedDeriv_two_comp_real hQ.contDiffAt (hv u hu)]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
    have hs := pow_le_pow_left₀ (abs_nonneg (deriv v u)) (hv1 u hu) 2
    rw [sq_abs] at hs
    calc
      _ ≤ M ^ 2 * ((M ^ 2 + 1) * Real.sqrt Real.pi * G * T ^ 2) +
          M * (M * Real.sqrt Real.pi * G * T) :=
        add_le_add
          (mul_le_mul hs (hb u hu).2.2 (norm_nonneg _) (sq_nonneg M))
          (mul_le_mul (hv2 u hu) (hb u hu).2.1 (norm_nonneg _) hM.le)
      _ ≤ (M ^ 2 * (M ^ 2 + 1) + M ^ 2) * (Real.sqrt Real.pi * G * T ^ 2) := by
        have h := mul_le_mul_of_nonneg_left (show T ≤ T ^ 2 by nlinarith)
          (show 0 ≤ M ^ 2 * Real.sqrt Real.pi * G by positivity)
        nlinarith
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hAM2
          (show 0 ≤ Real.sqrt Real.pi * G * T ^ 2 by positivity)
        nlinarith

def atkinsonRootLogProfile (u : ℝ) : ℝ := 2 * Real.log u + Real.log (2 * Real.pi)

theorem zetaQuadraticLogGaussian_root_rescale {T u : ℝ}
    (hT : 0 < T) (hu : 0 < u) (G : ℝ) :
    zetaGaussianQuadraticIntegral T G
      (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi))) =
        zetaGaussianQuadraticIntegral T G (atkinsonRootLogProfile u) := by
  unfold atkinsonRootLogProfile
  congr 1
  rw [Real.log_mul hT.ne' (pow_ne_zero 2 hu.ne'), Real.log_pow,
    Real.log_div hT.ne' (by positivity : 2 * Real.pi ≠ 0)]
  ring

theorem exists_intervalC2Bound_zetaQuadraticLogGaussian_root :
    ∃ C : ℝ, 0 < C ∧ ∀ T G : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      IntervalC2Bound (fun u => zetaGaussianQuadraticIntegral T G
        (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi)))) (1 / 4) 1 (C * G) T := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_quadraticGaussian_profile
    (v := atkinsonRootLogProfile) (a := 1 / 4) (b := 1) (by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      unfold atkinsonRootLogProfile
      fun_prop (disch := exact hu0.ne'))
  refine ⟨C, hC, ?_⟩
  intro T G hT hG hGT
  apply (hbound T G hT hG hGT).congr_of_eventuallyEq
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  filter_upwards [Ioi_mem_nhds hu0] with y hy
  exact (zetaQuadraticLogGaussian_root_rescale (by linarith) hy G).symm

end TaoTrudgianYang2025
