import Dubon2026.CuspRankinMean
import Dubon2026.PrimitiveArithmeticConcentration

/-! # Genuine cusp concentration with the mean-square input discharged

The actual Rankin mean is proved analytically. GeneralRankinSelberg separately proves
the sharp general-level remainder. Sato–Tate remains an explicit unproved arithmetic
input here, so these deductions do not close the unconditional modular application.
-/

namespace Dubon2026

open UpperHalfPlane ModularForm CongruenceSubgroup Filter Set MeasureTheory
open scoped MatrixGroups CongruenceSubgroup Topology

noncomputable section

/-- The genuine cusp concentration conclusions follow from Sato–Tate and real unramified coefficients, using the proved mean. -/
theorem cusp_concentration_of_sato_tate {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (qExpansion 1 f).coeff 1 = 1) (hk : 0 < k)
    (hreal : ∀ p, Nat.Prime p → ¬p ∣ Q → (normalizedCuspCoefficients f p).im = 0)
    (hST : Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f p).re))
      atTop (𝓝 satoTateProbability)) :
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
  have hd := sato_tate_selected_prime_density (Nat.pos_of_neZero Q) hreal hST
  exact cusp_concentration_of_mean_prime_density f hf
    (tendsto_cusp_square_mean f hk) satoTateBandDensity_pos hd


/-- For actual primitive forms, Hecke adjointness discharges reality and only Sato–Tate remains an explicit arithmetic input. -/
theorem primitive_concentration_of_sato_tate {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k)
    (hST : Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability)) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f.toCuspForm))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f.toCuspForm f.normalized)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f.toCuspForm))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (cuspCoefficients f.toCuspForm) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (cuspCoefficients f.toCuspForm) N)) *
        ((verticalZeroCount (cuspCoefficients f.toCuspForm) N hN (f.normalized.trans_ne one_ne_zero) l u T : ℝ) /
          (2 * T))) atTop
        (𝓝 (((jessenProbability (a := cuspCoefficients f.toCuspForm) f.normalized N : Measure ℝ) (Ioo l u)).toReal))) := by
  have hreal : ∀ p, Nat.Prime p → ¬p ∣ Q →
      (normalizedCuspCoefficients f.toCuspForm p).im = 0 := by
    intro p hp hpQ
    exact primitiveCuspForm_normalizedCoefficient_im f p (hp.coprime_iff_not_dvd.mpr hpQ)
  exact cusp_concentration_of_sato_tate f.toCuspForm f.normalized
    hk hreal hST


end
end Dubon2026
