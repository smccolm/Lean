import TaoTrudgianYang2025.BetaDualPowerWindows

/-!
# A physical-source beta bound for each stationary chart

The dual parameter and length are no longer independent hypotheses.
Their power windows and large-parameter threshold follow from the
original N,T window; chart scale factors enter only the uniform constant.
-/

noncomputable section

open Set Expdb Filter
open scoped NNReal BigOperators

namespace TaoTrudgianYang2025

theorem sourceStationaryChart_physical_bound
    {α : ℝ≥0} {β σ : ℝ}
    (hβ : IsExponentSumBoundNonAsymptotic α β) (hσ : 0 < σ)
    (j : ℕ) (hj : j ∈ positiveSlopeChartIndices (modelPhaseSlopeMesh σ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ min (modelPhaseCurvatureLower σ) 1 ∧
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 ∧
      ∃ P : ℕ, 2 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
          C ≤ T → 0 < N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
          T^(1-(α : ℝ)-δ) ≤ N → N ≤ T^(1-(α : ℝ)+δ) →
          (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N →
          IsApproximateModelPhaseFunction F σ P δ →
          ‖∑ q ∈ positiveSlopeChartFiber (modelPhaseSharpStationarySet F T N a b)
              (modelPhaseSlopeMesh σ) N T j, modelPhaseStationaryMainTerm F T N q‖ ≤
            C*(N/Real.sqrt T)*T^(β+ε) := by
  obtain ⟨d,hd,hsmall,hpos,P,hP,C,hC,hchart⟩ :=
    sourceStationaryChart_bound_of_exponentSumBound hβ hσ j hj hε
  let A := positiveSlopeChartScale (modelPhaseSlopeMesh σ) j
  have hA : 0 < A := (positiveSlopeChartScale_bounds (modelPhaseSlopeMesh_pos σ) hj).1
  obtain ⟨M,hM⟩ := eventually_atTop.1
    (eventually_modelPhaseDual_power_windows (σ := σ) hA hd (α : ℝ) C)
  let B := 2*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹*C*
    (A^(1-σ⁻¹))^(β+ε)
  let K := max 1 (max M B)
  have hK : 1 ≤ K := le_max_left _ _
  have hMK : M ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hBK : B ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hhalf : d/2 ≤ d := by linarith
  refine ⟨d/2,by positivity,hhalf.trans hsmall,hhalf.trans hpos,P,hP,K,hK,?_⟩
  intro T N F a b hTK hN ha hb hlow hhigh hlong hF
  have hT : 0 < T := zero_lt_one.trans_le (hK.trans hTK)
  obtain ⟨hTC,hwindow⟩ := hM T (hMK.trans hTK)
  obtain ⟨hlowd,hhighd⟩ := hwindow N hN hlow hhigh
  have hbnd := hchart T N F a b hT hN ha hb hlong
    (approximateModelPhase_mono hF le_rfl hhalf) hTC hlowd hhighd
  apply hbnd.trans
  calc
    2*((N/Real.sqrt T)*(Real.sqrt (modelPhaseCurvatureLower σ))⁻¹)*
        C*(modelPhaseDualParameter σ A T)^(β+ε) =
      B*(N/Real.sqrt T)*T^(β+ε) := by
        unfold modelPhaseDualParameter B
        rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) hT.le]
        ring
    _ ≤ K*(N/Real.sqrt T)*T^(β+ε) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBK (by positivity)) (Real.rpow_nonneg hT.le _)

end TaoTrudgianYang2025
