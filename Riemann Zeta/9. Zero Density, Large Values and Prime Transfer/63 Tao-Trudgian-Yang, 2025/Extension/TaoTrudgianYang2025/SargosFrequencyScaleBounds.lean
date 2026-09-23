import TaoTrudgianYang2025.SargosFrequencyWindows

/-! The actual quartic frequency is linked to both terms of the exponent-pair estimate. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosSextupleFrequency_le {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    |(sargosQuarticDifference q:ℝ)|/12 ≤ (H:ℝ)^4 := by
  have h := sargosQuarticDifference_abs_le q
  nlinarith [show (0:ℝ) ≤ (H:ℝ)^4 by positivity]

theorem sargosLargeFrequency_pos {H : ℕ} (hH : 1 ≤ H)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : q ∈ sargosLargeFrequencySextuples H) :
    0 < |(sargosQuarticDifference q:ℝ)| ∧ (H:ℝ)^3 ≤ |(sargosQuarticDifference q:ℝ)|/12 := by
  have h := (Finset.mem_filter.mp hq).2
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  constructor
  · exact (show 0 < 12*(H:ℝ)^3 by positivity).trans h
  · linarith

theorem sargosTransformedFrequency_main_le {σ N T k ε : ℝ} {H : ℕ}
    (hσ : 0 < σ) (hN : 0 < N) (hT : 0 < T) (hke : 0 ≤ k+ε)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    (sargosScaledTransformedTime σ N (|(sargosQuarticDifference q:ℝ)|/12) T/N)^(k+ε) ≤
      (modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε) := by
  have hD := modelPhaseJetCoefficient_pos hσ 4
  apply Real.rpow_le_rpow
  · unfold sargosScaledTransformedTime
    positivity
  · unfold sargosScaledTransformedTime
    have ht := sargosSextupleFrequency_le q
    have hm := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ T*modelPhaseJetCoefficient σ 4/N^5 by positivity)
    convert hm using 1 <;> field_simp
  · exact hke

theorem sargosTransformedFrequency_secondary_eq {σ N T : ℝ} {H : ℕ}
    (hσ : 0 < σ) (hN : 0 < N) (hT : 0 < T)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : 0 < |(sargosQuarticDifference q:ℝ)|) :
    N/sargosScaledTransformedTime σ N (|(sargosQuarticDifference q:ℝ)|/12) T =
      (N^5/(modelPhaseJetCoefficient σ 4*T))*(12/|(sargosQuarticDifference q:ℝ)|) := by
  have hD := modelPhaseJetCoefficient_pos hσ 4
  unfold sargosScaledTransformedTime
  field_simp

end TaoTrudgianYang2025
