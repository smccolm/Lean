import TaoTrudgianYang2025.SargosLargeFrequencyContribution
import TaoTrudgianYang2025.SargosSmallFrequencyContribution

/-! The full genuine interior correlation bound, including small and large frequencies. -/

noncomputable section

open Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_model_interior_correlation_bound {k l σ ε : ℝ}
    (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (H M a : ℕ) (F : ℝ → ℝ) (T N : ℝ),
        1 ≤ H → H ≤ M → 1 ≤ N → N ≤ (a:ℝ) → (a:ℝ)+M ≤ 2*N → 0 < T →
        IsApproximateModelPhaseFunction F σ P δ → (H:ℝ)^3/N^2 ≤ η →
        sargosInteriorSextupleCorrelation (heathBrownPhysicalPhase F T N a 1) M H ≤
          C*((M:ℝ)*(H:ℝ)^(3+ε)+
            (H:ℝ)^(4+ε)*(modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε)+
            (N^5/(modelPhaseJetCoefficient σ 4*T))*(H:ℝ)^ε) := by
  obtain ⟨δ,hδ,P,hP,η,hη,C,hC,hlarge⟩ := sargos_large_frequency_contribution hkl hσ hε
  obtain ⟨B,hB,hsmall⟩ := sargos_small_frequency_contribution ε hε
  refine ⟨δ,hδ,P,hP,η,hη,B+C,by linarith,?_⟩
  intro H M a F T N hH hHM hN ha hb hT hF hscale
  have hL := hlarge H M a F T N hH hHM hN ha hb hT hF hscale
  have hS := hsmall H hH M (heathBrownPhysicalPhase F T N a 1)
  have hpart := sargosFrequencySextuples_partition H
  unfold sargosInteriorSextupleCorrelation
  rw [← hpart.1,Finset.sum_union hpart.2]
  have hsum := add_le_add hS hL
  have hD := modelPhaseJetCoefficient_pos hσ 4
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hA : 0 ≤ (M:ℝ)*(H:ℝ)^(3+ε) := by positivity
  have hmain : 0 ≤ (H:ℝ)^(4+ε)*
      (modelPhaseJetCoefficient σ 4*T*(H:ℝ)^4/N^5)^(k+ε)*N^(l+ε) := by positivity
  have hsecondary : 0 ≤ (N^5/(modelPhaseJetCoefficient σ 4*T))*(H:ℝ)^ε := by positivity
  have hs := mul_nonneg (show 0 ≤ C by linarith) hA
  have hl := mul_nonneg (show 0 ≤ B by linarith) (add_nonneg hmain hsecondary)
  nlinarith only [hs,hl,hsum]

end TaoTrudgianYang2025
