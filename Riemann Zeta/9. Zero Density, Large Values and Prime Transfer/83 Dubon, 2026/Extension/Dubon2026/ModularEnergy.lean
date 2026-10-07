import Dubon2026.GeneralRankinSelberg
import Dubon2026.RankinSelbergEnergyConsequences

/-! # The unconditional source Rankin--Selberg energy lemma at every positive level -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The actual normalized cusp coefficients satisfy all three source weighted-energy regimes, with the strictly positive genuine Rankin residue and no arithmetic estimate supplied as a premise. -/
theorem general_cusp_weighted_rankin_selberg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
      (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ =>
        (coefficientEnergy (normalizedCuspCoefficients f) N σ -
          cuspRankinResidue f * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
            (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
        |coefficientEnergy (normalizedCuspCoefficients f) N (1 / 2) - cuspRankinResidue f * Real.log N| ≤ B) ∧
      (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        0 ≤ coefficientEnergy (normalizedCuspCoefficients f) N σ ∧
          coefficientEnergy (normalizedCuspCoefficients f) N σ ≤ B) := by
  obtain ⟨C, hC, hb⟩ := exists_general_cusp_square_three_fifths f hk
  exact ⟨cuspRankinResidue_pos f (by omega) hf, rankin_selberg_weighted_energy hC.le hb⟩

/-- The actual three-fifths remainder supplies the literal source Abel error for every real sigma, including zero and the logarithmic transition. -/
theorem exists_general_cusp_weighted_energy_error {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ σ : ℝ,
      |coefficientEnergy (normalizedCuspCoefficients f) N σ - weightedEnergyMain (cuspRankinResidue f) N σ| ≤
        C * ((N : ℝ) ^ ((3 / 5 : ℝ) - 2 * σ) +
          2 * |σ| * ∫ x : ℝ in Set.Ioc (1 : ℝ) N, x ^ ((3 / 5 : ℝ) - 2 * σ - 1)) := by
  obtain ⟨C, hC, hb⟩ := exists_general_cusp_square_three_fifths f hk
  exact ⟨C, hC, fun _ hN σ => weighted_energy_error_bound hb hN σ⟩

/-- At sigma=3/10 the genuine source error integral is precisely logarithmic, with an actual form-dependent constant. -/
theorem exists_general_cusp_weighted_energy_three_tenths {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |coefficientEnergy (normalizedCuspCoefficients f) N (3 / 10) -
        weightedEnergyMain (cuspRankinResidue f) N (3 / 10)| ≤ C * (1 + (3 / 5) * Real.log N) := by
  obtain ⟨C, hC, hb⟩ := exists_general_cusp_weighted_energy_error f hk
  refine ⟨C, hC, fun N hN => ?_⟩
  have he := hb N hN (3 / 10)
  norm_num only [show (3 / 5 : ℝ) - 2 * (3 / 10) = 0 by norm_num,
    zero_sub, Real.rpow_zero, show |(3 / 10 : ℝ)| = 3 / 10 by norm_num,
    show (2 : ℝ) * (3 / 10) = 3 / 5 by norm_num] at he
  rw [integral_inv_Ioc_one hN] at he
  exact he

/-- At sigma=0 the actual weighted energy retains the full three-fifths Rankin--Selberg error. -/
theorem exists_general_cusp_weighted_energy_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      |coefficientEnergy (normalizedCuspCoefficients f) N 0 - cuspRankinResidue f * N| ≤
        C * (N : ℝ) ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_general_cusp_weighted_energy_error f hk
  refine ⟨C, hC, fun N hN => ?_⟩
  simpa only [weightedEnergyMain, mul_zero, sub_zero, Real.rpow_one, abs_zero, zero_mul, add_zero] using hb N hN 0

end
end Dubon2026
