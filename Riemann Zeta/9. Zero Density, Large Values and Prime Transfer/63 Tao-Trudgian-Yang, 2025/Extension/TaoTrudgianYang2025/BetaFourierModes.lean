import TaoTrudgianYang2025.BetaSharpCutoff
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Physical Fourier-mode normalization and convergence

Each mode is the original oscillatory integral, with its exact factor N
after x=N*u. Schwartz decay proves genuine absolute summability on the
integer frequency lattice; no finite truncation is assumed.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped FourierTransform ContDiff BigOperators

namespace TaoTrudgianYang2025

def modelPhaseNormalizedMode (χ F : ℝ → ℝ) (T q : ℝ) : ℂ :=
  ∫ u : ℝ, (χ u : ℂ)*(𝐞 (T*F u-q*u) : ℂ)

theorem modelPhaseFourierMode_eq_normalized
    (χ F : ℝ → ℝ) (T r : ℝ) {N : ℝ} (hN : 0 < N) :
    modelPhaseFourierMode χ F T N r = N • modelPhaseNormalizedMode χ F T (r*N) := by
  have he : (fun x : ℝ =>
      (χ (x/N) : ℂ)*(𝐞 (T*F (x/N)-(r*N)*(x/N)) : ℂ)) =
      (fun x : ℝ => (χ (x/N) : ℂ)*
        (𝐞 (modelPhaseFrequencyPhase F T N r x) : ℂ)) := by
    funext x
    congr 2
    unfold modelPhaseFrequencyPhase
    field_simp
  unfold modelPhaseFourierMode modelPhaseNormalizedMode
  rw [← he,Measure.integral_comp_div
    (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*F u-(r*N)*u) : ℂ)) N,abs_of_pos hN]

theorem norm_modelPhaseFourierMode_le
    (χ F : ℝ → ℝ) (T r : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖modelPhaseFourierMode χ F T N r‖ ≤ N * ∫ u : ℝ, |χ u| := by
  unfold modelPhaseFourierMode
  calc
    ‖∫ x : ℝ, (χ (x/N) : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r x) : ℂ)‖ ≤
        ∫ x : ℝ, ‖(χ (x/N) : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r x) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = N * ∫ u : ℝ, |χ u| := by
      simp only [norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs]
      rw [Measure.integral_comp_div (fun u : ℝ => |χ u|) N,abs_of_pos hN,smul_eq_mul]

theorem summable_modelPhaseFourierMode
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T : ℝ) :
    Summable (fun r : ℤ => modelPhaseFourierMode χ F T N r) := by
  let f := modelPhaseWeightedSchwartz hχ hs hF hN T
  have hdecay := (𝓕 f).isBigO_cocompact_rpow (-(2 : ℝ))
  have hsum := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    (hdecay.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [f,Function.comp_def,Real.norm_eq_abs,modelPhaseWeightedSchwartz_fourier] using hsum

theorem summable_norm_modelPhaseFourierMode
    {χ F : ℝ → ℝ} {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T : ℝ) :
    Summable (fun r : ℤ => ‖modelPhaseFourierMode χ F T N r‖) :=
  (summable_modelPhaseFourierMode hχ hs hF hN T).norm

end TaoTrudgianYang2025
