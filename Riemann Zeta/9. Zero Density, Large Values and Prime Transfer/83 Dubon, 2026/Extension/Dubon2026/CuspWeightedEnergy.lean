import Dubon2026.MeanWeightedEnergy
import Dubon2026.CuspRankinMean

/-! # The genuine cusp weighted energies away from the central exponent -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The entire left-hand weighted Rankin energy asymptotic follows from the proved actual mean,
including σ=0 and σ=3/10, without a quantitative Rankin remainder premise. -/
theorem cusp_weighted_energy_left {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {σ : ℝ} (hσ : σ < 1 / 2) :
    Tendsto (fun N : ℕ => (coefficientEnergy (normalizedCuspCoefficients f) N σ -
      cuspRankinResidue f * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0) :=
  weighted_energy_left_of_linear_littleO (cusp_squareSummatory_sub_main_isLittleO f hk) hσ

/-- Above one half the actual weighted normalized coefficient energy is uniformly bounded. -/
theorem cusp_weighted_energy_right {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 0 ≤ coefficientEnergy (normalizedCuspCoefficients f) N σ ∧
      coefficientEnergy (normalizedCuspCoefficients f) N σ ≤ B :=
  weighted_energy_right_of_mean (tendsto_cusp_square_mean f hk) hσ

end
end Dubon2026
