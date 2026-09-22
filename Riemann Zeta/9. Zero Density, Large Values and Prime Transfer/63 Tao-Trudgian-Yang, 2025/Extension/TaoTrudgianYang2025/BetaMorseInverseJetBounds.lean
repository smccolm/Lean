import TaoTrudgianYang2025.BetaMorseInverseJets

/-!
# Uniform higher derivative bounds for the actual quadratic inverse

For each order, an explicit finite original-model order suffices.
Constants depend only on sigma and that order, on the full moving Morse image.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def morseInverseJetMagnitude (σ : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => Real.sqrt (σ+1)/modelPhaseCurvatureLower σ
  | n+2 => morseCoordinateDerivativeBound σ (n+1)

def morseInverseJetOrder : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => morseCoordinateDerivativeOrder (n+1)

def morseInverseJetBudget (σ : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), morseInverseJetMagnitude σ j

def morseInverseDerivativeOrder (n : ℕ) : ℕ :=
  1+∑ j ∈ Finset.range (inversePhaseOrder (inversePhaseDerivativeExpression n)+1),
    morseInverseJetOrder j

def morseInverseDerivativeBound (σ : ℝ) (n : ℕ) : ℝ :=
  inversePhaseMagnitude (inversePhaseDerivativeExpression n)
    (morseInverseJetBudget σ (inversePhaseOrder (inversePhaseDerivativeExpression n)))

theorem morseInverseJetMagnitude_nonneg {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 ≤ morseInverseJetMagnitude σ j := by
  match j with
  | 0 => norm_num [morseInverseJetMagnitude]
  | 1 => exact div_nonneg (Real.sqrt_nonneg _) (modelPhaseCurvatureLower_pos hσ).le
  | n+2 => exact morseCoordinateDerivativeBound_nonneg σ (n+1)

theorem morseInverseJetMagnitude_le_budget {σ : ℝ} (hσ : 0 < σ) {K j : ℕ} (hj : j ≤ K) :
    morseInverseJetMagnitude σ j ≤ morseInverseJetBudget σ K :=
  Finset.single_le_sum (fun k _ => morseInverseJetMagnitude_nonneg hσ k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

theorem morseInverseDerivativeOrder_pos (n : ℕ) : 1 ≤ morseInverseDerivativeOrder n := by
  unfold morseInverseDerivativeOrder
  omega

theorem morseInverseJetOrder_le_derivativeOrder {n j : ℕ}
    (hj : j ≤ inversePhaseOrder (inversePhaseDerivativeExpression n)) :
    morseInverseJetOrder j ≤ morseInverseDerivativeOrder n := by
  have h := Finset.single_le_sum (f := morseInverseJetOrder)
    (s := Finset.range (inversePhaseOrder (inversePhaseDerivativeExpression n)+1))
    (fun k _ => Nat.zero_le (morseInverseJetOrder k))
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  unfold morseInverseDerivativeOrder
  omega

theorem morseInverseDerivativeBound_nonneg {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 ≤ morseInverseDerivativeBound σ n :=
  inversePhaseMagnitude_nonneg _ (Finset.sum_nonneg fun j _ => morseInverseJetMagnitude_nonneg hσ j)

theorem modelPhaseMorseInverseJet_abs_le
    {F : ℝ → ℝ} {σ δ v z : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hP : 1 ≤ P) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (j : ℕ) (hj : morseInverseJetOrder j ≤ P) :
    |modelPhaseMorseInverseJet F v z j| ≤ morseInverseJetMagnitude σ j := by
  have hF₁ := approximateModelPhase_mono hF hP le_rfl
  have hu := modelPhaseMorseInverse_mem hz
  match j with
  | 0 =>
      change |modelPhaseMorseInverse F v z| ≤ 2
      rw [abs_of_pos (zero_lt_one.trans hu.1)]
      exact hu.2.le
  | 1 =>
      change |(deriv (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z))⁻¹| ≤ _
      rw [← (modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF₁ hv hz).hasDerivAt.deriv,
        abs_of_pos (modelPhaseMorseInverse_deriv_pos hσ hδ hF₁ hv hz)]
      exact (modelPhaseMorseInverse_deriv_bounds hσ hδ hF₁ hv hz).2
  | n+2 =>
      exact modelPhaseMorseCoordinate_iteratedDeriv_bound hσ hδ hF hv hu (n+1) hj

theorem modelPhaseMorseInverse_iteratedDeriv_bound
    {F : ℝ → ℝ} {σ δ v z : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (n : ℕ) (hP : morseInverseDerivativeOrder n ≤ P) :
    |iteratedDeriv n (modelPhaseMorseInverse F v) z| ≤
      morseInverseDerivativeBound σ n := by
  have hP₁ := (morseInverseDerivativeOrder_pos n).trans hP
  rw [iteratedDeriv_modelPhaseMorseInverse_formula hσ hδ
    (approximateModelPhase_mono hF hP₁ le_rfl) hv hz n]
  apply inversePhaseEval_abs_le
  intro j hj
  exact (modelPhaseMorseInverseJet_abs_le hσ hδ hP₁ hF hv hz j
    ((morseInverseJetOrder_le_derivativeOrder hj).trans hP)).trans
      (morseInverseJetMagnitude_le_budget hσ hj)

end TaoTrudgianYang2025
