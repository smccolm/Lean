import TaoTrudgianYang2025.AtkinsonAmplitudeIntegral

/-!
# Uniform variation of the actual power-weighted source amplitude

The fixed profile contains the real power and the actual Mellin weight.
Rescaling proves its bound before T, G, L and the carrier are chosen.
The cutoff, unit Gamma factor and damped Gaussian are all retained.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def atkinsonPowerProfile (α u : ℝ) : ℂ :=
  ((u ^ (-α) : ℝ) : ℂ) * zetaMainMellinProfile u

def atkinsonPowerWeight (T G L α x : ℝ) : ℂ :=
  ((T ^ (-α) : ℝ) : ℂ) * atkinsonPowerProfile α (x / T) *
    (zetaDivisorBandCutoff T G L x : ℂ) * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem contDiffAt_atkinsonPowerProfile (α : ℝ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ 1 (atkinsonPowerProfile α) u := by
  have hm := contDiffAt_zetaMainMellinProfile hu
  have hp : ContDiffAt ℝ 1 (fun v : ℝ => v ^ (-α)) u := by
    fun_prop (disch := exact hu.ne')
  unfold atkinsonPowerProfile
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u hp).mul hm

theorem sqrt_mul_exp_neg_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * Real.exp (-Real.log x / 2) = 1 := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem atkinsonPowerWeight_eq_amplitude {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
    (G L α : ℝ) :
    atkinsonPowerWeight T G L α x =
      (Real.sqrt x : ℂ) * ((x ^ (-α) : ℝ) : ℂ) * zetaAtkinsonAmplitude T G L x := by
  have he : T ^ (-α) * (x / T) ^ (-α) = x ^ (-α) := by
    rw [← Real.mul_rpow hT.le (by positivity), mul_div_cancel₀ _ hT.ne']
  have hs : (Real.sqrt x : ℂ) * (Real.exp (-Real.log x / 2) : ℂ) = 1 := by
    exact_mod_cast sqrt_mul_exp_neg_half_log hx
  unfold atkinsonPowerWeight atkinsonPowerProfile zetaAtkinsonAmplitude
  rw [zetaDivisorWeight_source_eq_profile hT hx]
  have heC : ((T ^ (-α) : ℝ) : ℂ) * (((x / T) ^ (-α) : ℝ) : ℂ) = ((x ^ (-α) : ℝ) : ℂ) := by
    exact_mod_cast he
  calc
    _ = (((T ^ (-α) : ℝ) : ℂ) * (((x / T) ^ (-α) : ℝ) : ℂ)) *
      (zetaMainMellinProfile (x / T) * (zetaDivisorBandCutoff T G L x : ℂ) *
        zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))) := by ring
    _ = _ := by
      rw [heC]
      linear_combination -((x ^ (-α) : ℝ) : ℂ) * zetaMainMellinProfile (x / T) *
        (zetaDivisorBandCutoff T G L x : ℂ) * zetaSquareReflectedGammaPhase T *
          zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi))) * hs

theorem exists_intervalC1Bound_atkinsonPowerWeight (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (atkinsonPowerWeight T G L α) (T / 16) T (C * G * T ^ (-α)) := by
  obtain ⟨C, hC, hprofile⟩ := exists_intervalC1Bound_rescaled
    (fun _ hu => contDiffAt_atkinsonPowerProfile α hu)
  refine ⟨128 * C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hG hGT hL
  have hab : T / 16 ≤ T := by linarith
  have ht : IntervalC1Bound (fun _ : ℝ => ((T ^ (-α) : ℝ) : ℂ)) (T / 16) T (T ^ (-α)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hT _)] using
      intervalC1Bound_const ((T ^ (-α) : ℝ) : ℂ) (T / 16) T
  have hp : IntervalC1Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (T / 16) T 1 := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC1Bound_const (zetaSquareReflectedGammaPhase T) (T / 16) T
  have h := (((ht.mul (hprofile T hT) hab).mul
    (intervalC1Bound_zetaDivisorBandCutoff hT hG hL hab) hab).mul hp hab).mul
      (intervalC1Bound_zetaQuadraticLogGaussian hT hG hGT) hab
  convert h using 1
  ring

end TaoTrudgianYang2025
