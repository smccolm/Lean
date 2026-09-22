import TaoTrudgianYang2025.BetaMorseJets

/-!
# Uniform all-order bounds for the actual quadratic coordinate

Every constant depends only on sigma and the requested derivative order.
No compactness bound depending on the individual phase or slope is used.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def morseJetMagnitude (σ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => Real.sqrt (σ+1)
  | 2 => (Real.sqrt (modelPhaseCurvatureLower σ))⁻¹
  | n+3 => 2*(modelPhaseJetCoefficient σ (n+2)+1)

def morseJetMagnitudeBudget (σ : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), morseJetMagnitude σ j

def morseCoordinateDerivativeOrder (n : ℕ) : ℕ :=
  inversePhaseOrder (morseDerivativeExpression n)+1

def morseCoordinateDerivativeBound (σ : ℝ) (n : ℕ) : ℝ :=
  inversePhaseMagnitude (morseDerivativeExpression n)
    (morseJetMagnitudeBudget σ (inversePhaseOrder (morseDerivativeExpression n)))

theorem morseJetMagnitude_nonneg (σ : ℝ) (j : ℕ) :
    0 ≤ morseJetMagnitude σ j := by
  match j with
  | 0 => exact zero_le_one
  | 1 => exact Real.sqrt_nonneg _
  | 2 => exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  | n+3 =>
      exact mul_nonneg (by norm_num)
        (add_nonneg (modelPhaseJetCoefficient_nonneg σ (n+2)) zero_le_one)

theorem morseJetMagnitude_le_budget (σ : ℝ) {K j : ℕ} (hj : j ≤ K) :
    morseJetMagnitude σ j ≤ morseJetMagnitudeBudget σ K :=
  Finset.single_le_sum (fun k _ => morseJetMagnitude_nonneg σ k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

theorem morseCoordinateDerivativeBound_nonneg (σ : ℝ) (n : ℕ) :
    0 ≤ morseCoordinateDerivativeBound σ n :=
  inversePhaseMagnitude_nonneg _ (Finset.sum_nonneg fun j _ => morseJetMagnitude_nonneg σ j)

theorem modelPhaseMorseJet_abs_le
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (j : ℕ) (hj : j ≤ P) :
    |modelPhaseMorseJet F v u j| ≤ morseJetMagnitude σ j := by
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hA := modelPhaseAveragedCurvature_bounds hσ hδ hF₁ hv hu
  match j with
  | 0 =>
      have hg := modelPhaseInverseSlope_mem hv
      change |u-modelPhaseInverseSlope F v| ≤ 1
      rw [abs_le]
      constructor <;> linarith [hu.1,hu.2,hg.1,hg.2]
  | 1 =>
      change |Real.sqrt (modelPhaseAveragedCurvature F v u)| ≤ Real.sqrt (σ+1)
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt hA.2
  | 2 =>
      change |(Real.sqrt (modelPhaseAveragedCurvature F v u))⁻¹| ≤
        (Real.sqrt (modelPhaseCurvatureLower σ))⁻¹
      rw [abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact inv_anti₀ (Real.sqrt_pos.mpr (modelPhaseCurvatureLower_pos hσ))
        (Real.sqrt_le_sqrt hA.1)
  | n+3 =>
      have h := abs_iteratedDeriv_modelPhaseAveragedCurvature_le hσ.le hF hv hu (n+1)
        (by omega)
      have hd : δ ≤ 1 := hδ.trans (min_le_right _ _)
      change |iteratedDeriv (n+1) (modelPhaseAveragedCurvature F v) u| ≤ _
      exact h.trans (by dsimp [morseJetMagnitude]; linarith)

theorem modelPhaseMorseCoordinate_iteratedDeriv_bound
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (n : ℕ) (hP : morseCoordinateDerivativeOrder n ≤ P) :
    |iteratedDeriv n (modelPhaseMorseCoordinate F v) u| ≤
      morseCoordinateDerivativeBound σ n := by
  have hP₁ : 1 ≤ P := by
    unfold morseCoordinateDerivativeOrder at hP
    omega
  rw [iteratedDeriv_modelPhaseMorseCoordinate_formula hσ hδ
    (approximateModelPhase_mono hF hP₁ le_rfl) hv hu n]
  apply inversePhaseEval_abs_le
  intro j hj
  exact (modelPhaseMorseJet_abs_le hσ hδ hP₁ hF hv hu j
    (by unfold morseCoordinateDerivativeOrder at hP; omega)).trans
      (morseJetMagnitude_le_budget σ hj)

end TaoTrudgianYang2025
