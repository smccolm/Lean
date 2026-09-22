import TaoTrudgianYang2025.ExponentPairSourceCorrelation
import TaoTrudgianYang2025.ExponentPair

/-!
# The actual exponent-pair consumer for source correlations

All shift-model and integer-endpoint conditions are derived from original
source data. The two physical dual-height conditions remain explicit:
this is the large-dual-parameter branch, not the full A-process.
-/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem sourceShiftCorrelation_bound_of_exponentPair
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1/2 ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N : ℝ) (a L r : ℕ),
          2 ≤ N → 0 < r → (r : ℝ) ≤ η₀*N →
          N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
          IsApproximateModelPhaseFunction F σ P δ →
          C ≤ σ*T*r/N → N-r ≤ σ*T*r/N →
          ‖sourceShiftCorrelation F T N a L r‖ ≤
            C*((σ*T*r/N)/(N-r))^(k+ε)*(N-r)^(l+ε) := by
  obtain ⟨d,hd,Q,hQ,C,hC,hbound⟩ :=
    (isExponentPairEstimate_iff_nonAsymptotic.mp hkl.estimate) ε hε
      (σ+1) (by linarith)
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,hmodel⟩ := aProcessShiftPhase_uniform_model hσ Q hd
  refine ⟨δ,hδ,Q+1,by omega,η₀,hη₀,hηhalf,C,hC,?_⟩
  intro F T N a L r hN hr hrN ha hb hF hTC hNT
  have hNpos : 0 < N := by linarith
  have hrhalf : (r : ℝ) ≤ N/2 :=
    hrN.trans (by nlinarith)
  have hNr : 1 ≤ N-(r : ℝ) := by linarith
  have hrlt : (r : ℝ) < N := by linarith
  have hra : r ≤ a := by exact_mod_cast (hrlt.le.trans ha)
  have hTpos : 0 < σ*T*r/N := zero_lt_one.trans_le (hC.trans hTC)
  by_cases hrL : r ≤ L
  · have hηpos : 0 < (r : ℝ)/N := div_pos (Nat.cast_pos.mpr hr) hNpos
    have hηcap : (r : ℝ)/N ≤ η₀ := (div_le_iff₀ hNpos).mpr hrN
    have hphase := hmodel F ((r : ℝ)/N) hF hηpos hηcap
    have hend := sourceShiftCorrelation_compressed_endpoints ha hb hrlt hrL
    have hsum := hbound (σ*T*r/N) (N-r) (aProcessShiftPhase F σ ((r : ℝ)/N))
      (a-r) ((a-r)+(L-r)) ⟨hTC,hNr,hNT,hphase,hend.1,hend.2⟩
    rw [norm_sourceShiftCorrelation_compressed_sum hNpos.ne'
      (zero_lt_one.trans_le hNr).ne' hσ.ne' hr hra hrL]
    exact hsum
  · rw [sourceShiftCorrelation_empty _ _ _ _ _ _ (by omega),norm_zero]
    exact mul_nonneg
      (mul_nonneg (zero_le_one.trans hC)
        (Real.rpow_nonneg (div_nonneg hTpos.le (zero_le_one.trans hNr)) _))
      (Real.rpow_nonneg (zero_le_one.trans hNr) _)

end TaoTrudgianYang2025
