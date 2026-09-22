import TaoTrudgianYang2025.BetaResonantSum

/-! Exact source beta endpoints. The lower endpoint-one bound is obtained
from an explicit coherent logarithmic sum in the original model family. -/

noncomputable section

open Expdb Filter Topology

namespace TaoTrudgianYang2025

theorem half_le_exponentSumGrowthExponent_one :
    (1 : ℝ)/2 ≤ exponentSumGrowthExponent 1 := by
  let N : VariableObject ℝ := fun i => (betaResonantScale i : ℝ)
  let a : VariableObject ℕ := betaResonantScale
  let b : VariableObject ℕ := fun i => betaResonantScale i+i
  have hN : ∀ i, 1 ≤ N i := betaResonantScale_one_le
  have htop : N.IsUnbounded :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i => zero_le_one.trans (hN i))).2 betaResonantScale_tendsto
  have hNT : IsPowerAsymptotic N N (↑(1 : NNReal) : ℝ) := isPowerAsymptotic_self N
  have hab : ∀ i, N i ≤ (a i : ℝ) ∧ (b i : ℝ) ≤ 2*N i := by
    intro i
    constructor
    · exact le_rfl
    · dsimp [b,N]
      push_cast
      linarith [betaResonantScale_index_le i]
  apply le_exponentSumGrowthExponent_of_logPhase_lower_bound 1
    hN hN htop hNT hab (by norm_num : (0 : ℝ) < 1/8)
  exact Filter.Eventually.of_forall fun i => by
    simpa [N,a,b,exponentialSum,logPhase,Real.sqrt_eq_rpow,
      div_eq_mul_inv,mul_comm] using norm_logPhase_resonant_sum_lower i

theorem exponentSumGrowthExponent_one :
    exponentSumGrowthExponent 1 = (1 : ℝ)/2 :=
  le_antisymm exponentSumGrowthExponent_one_le_half half_le_exponentSumGrowthExponent_one

theorem exponentSumGrowthExponent_endpoints :
    exponentSumGrowthExponent 0 = 0 ∧ exponentSumGrowthExponent 1 = (1 : ℝ)/2 :=
  ⟨exponentSumGrowthExponent_zero,exponentSumGrowthExponent_one⟩

end TaoTrudgianYang2025
