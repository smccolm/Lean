import TaoTrudgianYang2025.BetaCoherentPowerWitness
import TaoTrudgianYang2025.BetaEndpoints

/-!
# The genuine beta lower bound needed by reflection

The bound beta(alpha)>=alpha-1/2 on [0,1] follows from actual coherent
model sums. Nonnegativity handles the left half and the exact endpoint
handles alpha=1; no reflected-beta conclusion is used in this proof.
-/

noncomputable section

open Expdb Filter
open scoped NNReal

namespace TaoTrudgianYang2025

theorem alpha_sub_half_le_of_exponentSumBoundNonAsymptotic
    {α : ℝ≥0} {β : ℝ} (hα : (α : ℝ) ≤ 1)
    (hβ : IsExponentSumBoundNonAsymptotic α β) :
    (α : ℝ)-1/2 ≤ β := by
  have hleast := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr hβ
  have hβnonneg : 0 ≤ β :=
    (isExponentSumBound_exponentSumGrowthExponent α).nonneg.trans hleast
  by_cases hhalf : (α : ℝ) ≤ 1/2
  · linarith
  by_cases hαone : (α : ℝ) = 1
  · have he : α = 1 := NNReal.coe_injective hαone
    rw [he,exponentSumGrowthExponent_one] at hleast
    linarith
  have hαpos : 0 < (α : ℝ) := by linarith
  have hαlt : (α : ℝ) < 1 := by
    rcases lt_or_eq_of_le hα with h | h
    · exact h
    · exact (hαone h).elim
  by_contra hfailure
  have hgap : β < (α : ℝ)-1/2 := lt_of_not_ge hfailure
  let ε := ((α : ℝ)-1/2-β)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexp : β+ε < (α : ℝ)-1/2 := by dsimp [ε]; linarith
  obtain ⟨δ,hd,P,_hP,C,hC,hbound⟩ := hβ ε hε 1 (by norm_num)
  obtain ⟨M,hM⟩ := eventually_atTop.1
    (eventually_const_mul_rpow_le_rpow (D := 16*C) hexp)
  obtain ⟨T,N,hT,hTB,hN,hscale,hend,hmodel,hlower⟩ :=
    exists_twistedLog_power_witness hαpos hαlt hd (max M C)
  have hTC : C ≤ T := (le_max_right _ _).trans hTB
  have hTM : M ≤ T := (le_max_left _ _).trans hTB
  have hlow : T^((α : ℝ)-δ) ≤ (N : ℝ) := by
    rw [← hscale]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hhigh : (N : ℝ) ≤ T^((α : ℝ)+δ) := by
    rw [← hscale]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hupper := hbound T N (twistedLogPhase (betaResonantCorrection T N))
    N (N+betaCoherentLength T N)
    ⟨hTC,hlow,hhigh,hmodel P,le_rfl,hend⟩
  have hdom := hM T hTM
  have hp : 0 < T^((α : ℝ)-1/2) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) _
  nlinarith

theorem alpha_sub_half_le_exponentSumGrowthExponent
    {α : ℝ≥0} (hα : (α : ℝ) ≤ 1) :
    (α : ℝ)-1/2 ≤ exponentSumGrowthExponent α :=
  alpha_sub_half_le_of_exponentSumBoundNonAsymptotic hα
    (exponentSumGrowthExponent_le_iff_nonAsymptotic.mp le_rfl)

end TaoTrudgianYang2025
