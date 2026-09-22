import TaoTrudgianYang2025.ExponentPairSourceCorrelation
import TaoTrudgianYang2025.ExponentPairAllHeights

/-!
# Source correlations without dual-height hypotheses

Every positive original height is covered by the proved low, transition
and large-height estimates. The compressed model and its integer
endpoints are derived from the original closed source interval.
-/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sourceShiftCorrelation_bound_allHeights
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/2 ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N : ℝ) (a L r : ℕ),
          0 < T → 2 ≤ N → 0 < r → (r : ℝ) ≤ η₀*N →
          N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          ‖sourceShiftCorrelation F T N a L r‖ ≤
            C*(((σ*T*r/N)/(N-r))^(k+ε)*(N-r)^(l+ε)+
              (N-r)/(σ*T*r/N)) := by
  obtain ⟨d,hd,Q,hQ,C,hC,hbound⟩ := hkl.allPositiveHeight_bound (by linarith : 0 < σ+1) hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,hmodel⟩ := aProcessShiftPhase_uniform_model hσ Q hd
  refine ⟨δ,hδ,Q+1,by omega,η₀,hη₀,hηhalf,C,hC,?_⟩
  intro F T N a L r hT hN hr hrN ha hb hF
  have hNpos : 0 < N := by linarith
  have hrhalf : (r : ℝ) ≤ N/2 := hrN.trans (by nlinarith)
  have hNr : 1 ≤ N-(r : ℝ) := by linarith
  have hrlt : (r : ℝ) < N := by linarith
  have hra : r ≤ a := by exact_mod_cast (hrlt.le.trans ha)
  have hdual : 0 < σ*T*r/N := div_pos
    (mul_pos (mul_pos hσ hT) (Nat.cast_pos.mpr hr)) hNpos
  by_cases hrL : r ≤ L
  · have hηpos : 0 < (r : ℝ)/N := div_pos (Nat.cast_pos.mpr hr) hNpos
    have hηcap : (r : ℝ)/N ≤ η₀ := (div_le_iff₀ hNpos).mpr hrN
    have hphase := hmodel F ((r : ℝ)/N) hF hηpos hηcap
    have hend := sourceShiftCorrelation_compressed_endpoints ha hb hrlt hrL
    have hsum := hbound (σ*T*r/N) (N-r) (aProcessShiftPhase F σ ((r : ℝ)/N))
      (a-r) ((a-r)+(L-r)) hdual hNr hend.1 hend.2 hphase
    rw [norm_sourceShiftCorrelation_compressed_sum hNpos.ne'
      (zero_lt_one.trans_le hNr).ne' hσ.ne' hr hra hrL]
    exact hsum
  · rw [sourceShiftCorrelation_empty _ _ _ _ _ _ (by omega),norm_zero]
    have hCpos := zero_lt_one.trans_le hC
    have hNrpos := zero_lt_one.trans_le hNr
    positivity

end TaoTrudgianYang2025
