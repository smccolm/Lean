import Dubon2026.PrimitiveCoefficientReality
import Dubon2026.CuspArithmeticConcentration

/-! # Actual primitive-form concentration with coefficient reality discharged

The Rankin–Selberg estimate and Sato–Tate equidistribution are explicit inputs to
this generic consumer. GeneralRankinSelberg separately proves the former; the latter
remains unproved. Reality is derived from actual Hecke adjointness.
-/

namespace Dubon2026

open UpperHalfPlane ModularForm CongruenceSubgroup Filter Set MeasureTheory Asymptotics
open scoped MatrixGroups CongruenceSubgroup Topology

noncomputable section

/-- Genuine primitive-form concentration from the two remaining displayed arithmetic inputs. -/
theorem primitive_concentration_of_rankin_selberg_sato_tate {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) {c : ℝ}
    (hRS : (fun x : ℝ => squareSummatory (normalizedCuspCoefficients f.toCuspForm) x - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ)))
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
  exact cusp_concentration_of_rankin_selberg_sato_tate f.toCuspForm f.normalized
    (Nat.pos_of_neZero Q) hRS hreal hST

end
end Dubon2026
