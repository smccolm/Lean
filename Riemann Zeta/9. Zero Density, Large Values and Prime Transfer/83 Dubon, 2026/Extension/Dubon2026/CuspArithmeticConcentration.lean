import Dubon2026.RankinSelbergInputBridge
import Dubon2026.SatoTatePrimeBlocks

/-! # Actual cusp concentration from individually displayed classical arithmetic inputs

Rankin–Selberg, unramified coefficient reality and Sato–Tate remain conditional.
All density, H1/H2, support, potential, probability and multiplicity transfers are derived.
-/

namespace Dubon2026

open UpperHalfPlane ModularForm CongruenceSubgroup Filter Set MeasureTheory Asymptotics
open scoped MatrixGroups CongruenceSubgroup Topology

noncomputable section

theorem cusp_concentration_of_rankin_selberg_sato_tate {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (qExpansion 1 f).coeff 1 = 1) (hQ : 0 < Q) {c : ℝ}
    (hRS : (fun x : ℝ => squareSummatory (normalizedCuspCoefficients f) x - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ)))
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
  have hd := sato_tate_selected_prime_density hQ hreal hST
  exact cusp_concentration_of_rankin_selberg_prime_density f hf hRS satoTateBandDensity_pos hd

end

end Dubon2026
