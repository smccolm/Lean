import TaoTrudgianYang2025.ZetaQuadraticLogGaussianVariation

/-!
# The complete actual amplitude of the logarithmic Voronoi main term

All factors are retained. Their proved derivative integrals give
O(G sqrt(T) log(T)) variation; the native reflection estimate supplies
the compensating factor 1/sqrt(T).
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def zetaAtkinsonMainWeight (T G L x : ℝ) : ℂ :=
  ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ) *
    (zetaDivisorBandCutoff T G L x : ℂ) * (Real.sqrt x : ℂ) *
      zetaMainMellinProfile (x / T) * zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem zetaAtkinsonMainWeight_eq_amplitude {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (G L : ℝ) :
    zetaAtkinsonMainWeight T G L x =
      (x : ℂ) * ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) *
        zetaAtkinsonAmplitude T G L x := by
  unfold zetaAtkinsonMainWeight zetaAtkinsonAmplitude
  rw [← zetaDivisorWeight_source_eq_profile hT hx, ← mul_exp_neg_half_log_eq_sqrt hx]
  push_cast
  ring

theorem zetaAtkinsonMainWeight_carrier {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (G L : ℝ) :
    zetaAtkinsonMainWeight T G L x * ((x : ℂ)⁻¹ *
      Complex.exp (((T * Real.log x - 2 * Real.pi * x : ℝ) : ℂ) * I)) =
        ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * zetaAtkinsonDivisorTest T G L x := by
  rw [zetaAtkinsonMainWeight_eq_amplitude hT hx G L,
    zetaAtkinsonDivisorTest_eq_amplitude_phase T G L hx]
  simp only [zetaAtkinsonPhase, mul_zero, zero_mul, add_zero]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp

theorem exists_intervalC1Bound_zetaAtkinsonMainWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
      0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (zetaAtkinsonMainWeight T G L) (T / 16) T
        (C * G * Real.sqrt T * Real.log T) := by
  obtain ⟨C, hC, hprofile⟩ := exists_intervalC1Bound_zetaMainMellinProfile
  refine ⟨768 * C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hlog hG hGT hL
  have hT0 : 0 < T := by linarith
  have hinterval : T / 16 ≤ T := by linarith
  have hphase : IntervalC1Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (T / 16) T 1 := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC1Bound_const (zetaSquareReflectedGammaPhase T) (T / 16) T
  have h := (((((intervalC1Bound_source_log hT).mul
    (intervalC1Bound_zetaDivisorBandCutoff hT0 hG hL hinterval) hinterval).mul
      (intervalC1Bound_source_sqrt hT0) hinterval).mul (hprofile T hT0) hinterval).mul
        hphase hinterval).mul (intervalC1Bound_zetaQuadraticLogGaussian hT0 hG hGT) hinterval
  apply h.mono
  have hp : 0 ≤ 256 * C * Real.sqrt Real.pi * G * Real.sqrt T := by positivity
  have hl := mul_le_mul_of_nonneg_left (sourceLogWeight_le_three_log hlog) hp
  convert hl using 1 <;> ring

end TaoTrudgianYang2025
