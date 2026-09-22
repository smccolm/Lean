import TaoTrudgianYang2025.ExponentPairIntegerOptimization
import TaoTrudgianYang2025.ExponentPairEpsilonBudget

/-!
# Optimized original-source A-process estimate

The actual source sum supplies both the finite differencing estimate
and the short-scale cardinality branch. The real optimum is explicitly
linked to T,N, and the selected shift is a natural number.
-/

noncomputable section

open Expdb

namespace TaoTrudgianYang2025

theorem source_exponentialSum_aProcess_bound
    {k l σ ε : ℝ} (hkl : ExponentPair k l) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ),
        2 ≤ N → N ≤ T → N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
        IsApproximateModelPhaseFunction F σ P δ →
        ‖exponentialSumAt F T N a (a+L)‖^2 ≤
          C*((T/N)^(k/(2*k+2)+ε)*N^(l/(2*k+2)+1/2+ε))^2 := by
  obtain ⟨δ,hδ,P,hP,η,hη,hηhalf,B,hB,hbound⟩ :=
    source_exponentialSum_differencing_bound hkl hσ hε
  let C₀ := 20*B/η
  have hC₀ : 1 ≤ C₀ := (le_div_iff₀ hη).mpr (by linarith)
  have hfactor : 1 ≤ 1+1/ε := by
    have hi : 0 < 1/ε := by positivity
    linarith
  refine ⟨δ,hδ,P,hP,C₀*(1+1/ε),by nlinarith,?_⟩
  intro F T N a L hN hNT ha hb hF
  have hN₁ : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hT := hNpos.trans_le hNT
  have hk : 0 ≤ k := hkl.inTriangle.1
  have hl : 0 ≤ l := by linarith [hkl.inTriangle.2.2.1]
  have hq : 0 ≤ k+ε := by linarith
  have hp : 0 ≤ l+ε := by linarith
  let R := aProcessOptimizationScale (k+ε) (l+ε) T N
  let M := (T/N^2)^(k+ε)*N^(l+ε)
  have hR : 0 < R := aProcessOptimizationScale_pos hT hNpos
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hRN : R ≤ N := aProcessOptimizationScale_le hq hp hN₁ hNT
  have hbalance : M*R^(k+ε+1) = N :=
    aProcessOptimizationScale_balance hq hT hNpos
  have hcard : ‖exponentialSumAt F T N a (a+L)‖ ≤ 3*N :=
    (norm_exponentialSumAt_le_add_one F T N a (a+L)).trans (by linarith)
  have htrivial : ‖exponentialSumAt F T N a (a+L)‖^2 ≤ 9*N^2 := by
    nlinarith [norm_nonneg (exponentialSumAt F T N a (a+L))]
  have hopt := integer_shift_optimization hNpos hM hR hq hRN hη
    (show η ≤ 1 by linarith) hB
    (show 1 ≤ 1+Real.log N by have := Real.log_nonneg hN₁; linarith)
    hbalance htrivial (fun H hH hHN => by
      have hh := hbound F T N a L H hN hNT hH hHN ha hb hF
      dsimp [M]
      convert hh using 1
      ring)
  have hcost : N^2/R =
      (T/N)^((k+ε)/(k+ε+1))*N^(1+(l+ε)/(k+ε+1)) :=
    aProcessOptimizationScale_cost hq hT hNpos
  have hratio : 1 ≤ T/N := (le_div_iff₀ hNpos).mpr (by simpa using hNT)
  calc
    _ ≤ C₀*(N^2/R)*(1+Real.log N) := hopt
    _ = C₀*((T/N)^((k+ε)/(k+ε+1))*N^(1+(l+ε)/(k+ε+1))*(1+Real.log N)) := by
      rw [hcost]
      ring
    _ ≤ C₀*((1+1/ε)*((T/N)^(k/(2*k+2)+ε)*N^(l/(2*k+2)+1/2+ε))^2) :=
      mul_le_mul_of_nonneg_left (aProcess_power_budget hk hl hε hratio hN₁)
        (zero_le_one.trans hC₀)
    _ = _ := by ring

end TaoTrudgianYang2025
