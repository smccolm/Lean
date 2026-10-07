import Dubon2026.CuspCentralTauberian
import Dubon2026.NewmanSquareAbel

/-! # The exact bounded central weighted cusp energy remainder -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The genuine central weighted cusp energy has a convergent renormalized remainder, equal to its Rankin regular part. -/
theorem tendsto_cusp_weighted_energy_center_error {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Tendsto (fun N : ℕ => coefficientEnergy (normalizedCuspCoefficients f) N (1 / 2) -
      cuspRankinResidue f * Real.log N) atTop (𝓝 ((cuspRankinRegular f 1).re)) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := Complex.continuous_re.continuousAt.tendsto.comp
    ((tendsto_cusp_square_error_integral f hk).comp ht)
  have hm := tendsto_cusp_square_mean f hk
  have hh := hm.add hi
  simp only [cuspSquareErrorLaplace_zero, Complex.sub_re, Complex.ofReal_re, add_sub_cancel] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  dsimp only [Function.comp_def]
  rw [coefficientEnergy_center_tauberian_identity _ _ hN, squareSummatory_nat]

/-- In particular, the literal central weighted energy is c_f log N plus a uniformly bounded error. -/
theorem cusp_weighted_energy_center {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      |coefficientEnergy (normalizedCuspCoefficients f) N (1 / 2) - cuspRankinResidue f * Real.log N| ≤ B := by
  have hh := (tendsto_cusp_weighted_energy_center_error f hk).norm
  obtain ⟨B, hb⟩ := hh.bddAbove_range
  refine ⟨max 0 B, le_max_left _ _, fun N => ?_⟩
  exact le_trans (by simpa only [Real.norm_eq_abs] using hb (mem_range_self N)) (le_max_right _ _)

end
end Dubon2026
