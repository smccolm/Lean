import Dubon2026.MeanSquareConcentration
import Dubon2026.CuspNormalization
import Dubon2026.ProbabilityShift

/-! # Conditional concentration for genuine cusp-form q-expansion coefficients

The two arithmetic limits in the public signature remain explicit. This file
proves their analytic consequences and the actual classical shift; it does not
claim Rankin–Selberg, Deligne or Sato–Tate for primitive non-CM eigenforms.
-/

namespace Dubon2026

open UpperHalfPlane ModularForm CongruenceSubgroup Filter Set MeasureTheory
open scoped MatrixGroups CongruenceSubgroup Topology

noncomputable section

/-- The actual unramified prime selection used in the source modular application. -/
def cuspPrimeSelection {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (p : ℕ) : Prop :=
  ¬p ∣ Q ∧ 1 ≤ ‖normalizedCuspCoefficients f p‖ ∧ ‖normalizedCuspCoefficients f p‖ ≤ 2

theorem cuspCoefficients_eq_shifted_normalized {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspCoefficients f = shiftedCoefficients (normalizedCuspCoefficients f) (((k : ℝ) - 1) / 2) := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [normalizedCuspCoefficients, shiftedCoefficients]
    rw [mul_assoc, ← Complex.cpow_add _ _ hnC]
    have he : ((-((k : ℝ) - 1) / 2 : ℝ) : ℂ) + ((((k : ℝ) - 1) / 2 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [he, Complex.cpow_zero, mul_one]

/-- Conditional normalized and classical weak limits for the actual cusp coefficients.
The mean-square and prime-density inputs are displayed individually, and H1/H2 are derived. -/
theorem cusp_concentration_of_mean_prime_density {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (qExpansion 1 f).coeff 1 = 1) {c density : ℝ}
    (hmean : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, ‖normalizedCuspCoefficients f n‖ ^ 2) / N) atTop (𝓝 c))
    (hdensity : 0 < density)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo (cuspPrimeSelection f) N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 density)) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f hf)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f) hf) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (cuspCoefficients f) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (cuspCoefficients f) N)) *
        ((verticalZeroCount (cuspCoefficients f) N hN (hf.trans_ne one_ne_zero) l u T : ℝ) /
          (2 * T))) atTop
        (𝓝 (((jessenProbability (a := cuspCoefficients f) hf N : Measure ℝ) (Ioo l u)).toReal))) := by
  have ha := normalizedCuspCoefficients_one f hf
  have hb : ∀ p, Nat.Prime p → cuspPrimeSelection f p →
      1 ≤ ‖normalizedCuspCoefficients f p‖ ∧ ‖normalizedCuspCoefficients f p‖ ≤ 2 := by
    intro p _ hp
    exact hp.2
  obtain ⟨hp, _, _, hw, he⟩ := mean_square_prime_density_concentration ha hmean hdensity hd hb
  have hne : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 1 < lastIndex (normalizedCuspCoefficients f) N := by
    filter_upwards [he] with N hN
    obtain ⟨hn, hm, _⟩ := hN
    exact ⟨hn, hm⟩
  have hclassp := shifted_normalizedJessen_limit hp (((k : ℝ) - 1) / 2)
  have hclassw := shifted_jessen_probability_limit ha hne hw (((k : ℝ) - 1) / 2)
  rw [← cuspCoefficients_eq_shifted_normalized f, classical_cusp_concentration_line] at hclassp
  rw [← jessenProbability_congr (cuspCoefficients_eq_shifted_normalized f) hf _,
    classical_cusp_concentration_line] at hclassw
  refine ⟨hp, hw, hclassp, hclassw, ?_⟩
  filter_upwards [hne] with N hn
  have hm : 1 < lastIndex (cuspCoefficients f) N := by
    simpa only [normalizedCuspCoefficients_lastIndex] using hn.2
  exact ⟨hn.1, hm, tendsto_normalized_verticalZeroCount hn.1 hf hm⟩

end

end Dubon2026
