import TaoTrudgianYang2025.BetaMorseWeightJets

/-!
# Uniform global bounds for every transformed-weight derivative

The finite original-cutoff derivative budget is visible. All other constants
and required original-phase orders depend only on sigma and the output order.
The estimate holds on the whole line, including the moving image boundary.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def morseWeightCutoffOrder (n : ℕ) : ℕ :=
  inversePhaseOrder (morseWeightDerivativeExpression n)

def morseWeightDerivativeOrder (n : ℕ) : ℕ :=
  1+∑ j ∈ Finset.range (morseWeightCutoffOrder n+2), morseInverseDerivativeOrder j

def morseWeightJetBudget (σ M : ℝ) (n : ℕ) : ℝ :=
  M+∑ j ∈ Finset.range (morseWeightCutoffOrder n+2), morseInverseDerivativeBound σ j

def morseWeightDerivativeBound (σ M : ℝ) (n : ℕ) : ℝ :=
  inversePhaseMagnitude (morseWeightDerivativeExpression n) (morseWeightJetBudget σ M n)

theorem morseWeightDerivativeOrder_pos (n : ℕ) : 1 ≤ morseWeightDerivativeOrder n := by
  unfold morseWeightDerivativeOrder
  omega

theorem morseWeightDerivativeBound_nonneg {σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ morseWeightDerivativeBound σ M n :=
  inversePhaseMagnitude_nonneg _ (add_nonneg hM
    (Finset.sum_nonneg fun j _ => morseInverseDerivativeBound_nonneg hσ j))

theorem morseWeight_inverseOrder_le {n j : ℕ} (hj : j ≤ morseWeightCutoffOrder n+1) :
    morseInverseDerivativeOrder j ≤ morseWeightDerivativeOrder n := by
  have h := Finset.single_le_sum (f := morseInverseDerivativeOrder)
    (s := Finset.range (morseWeightCutoffOrder n+2))
    (fun k _ => Nat.zero_le (morseInverseDerivativeOrder k))
    (Finset.mem_range.mpr (by omega : j < morseWeightCutoffOrder n+2))
  unfold morseWeightDerivativeOrder
  omega

theorem morseWeightJet_abs_le
    {χ F : ℝ → ℝ} {σ δ v z M : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hM : 0 ≤ M) (n : ℕ) (hP : morseWeightDerivativeOrder n ≤ P)
    (hχ : ∀ u ∈ Ioo (1 : ℝ) 2, ∀ k ≤ morseWeightCutoffOrder n, |iteratedDeriv k χ u| ≤ M)
    (j : ℕ) (hj : j ≤ morseWeightCutoffOrder n) :
    |morseWeightJet χ F v z j| ≤ morseWeightJetBudget σ M n := by
  unfold morseWeightJet
  have hsum : 0 ≤ ∑ k ∈ Finset.range (morseWeightCutoffOrder n+2),
      morseInverseDerivativeBound σ k :=
    Finset.sum_nonneg fun k _ => morseInverseDerivativeBound_nonneg hσ k
  split_ifs with he
  · exact (hχ _ (modelPhaseMorseInverse_mem hz) (j/2) (by omega)).trans
      (by unfold morseWeightJetBudget; linarith)
  · have hindex : j/2+1 ≤ morseWeightCutoffOrder n+1 := by omega
    have hi := modelPhaseMorseInverse_iteratedDeriv_bound hσ hδ hF hv hz (j/2+1)
      ((morseWeight_inverseOrder_le hindex).trans hP)
    have hb := Finset.single_le_sum (f := morseInverseDerivativeBound σ)
      (s := Finset.range (morseWeightCutoffOrder n+2))
      (fun k _ => morseInverseDerivativeBound_nonneg hσ k)
      (Finset.mem_range.mpr (by omega : j/2+1 < morseWeightCutoffOrder n+2))
    exact hi.trans (by unfold morseWeightJetBudget; linarith)

theorem modelPhaseMorseWeight_iteratedDeriv_bound
    {χ F : ℝ → ℝ} {σ δ v M : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hM : 0 ≤ M)
    (n : ℕ) (hP : morseWeightDerivativeOrder n ≤ P)
    (hb : ∀ u ∈ Ioo (1 : ℝ) 2, ∀ k ≤ morseWeightCutoffOrder n, |iteratedDeriv k χ u| ≤ M)
    (z : ℝ) :
    |iteratedDeriv n (modelPhaseMorseWeight χ F v) z| ≤ morseWeightDerivativeBound σ M n := by
  have hP₁ := (morseWeightDerivativeOrder_pos n).trans hP
  have hF₁ := approximateModelPhase_mono hF hP₁ le_rfl
  by_cases hz : z ∈ modelPhaseMorseRange F v
  · rw [iteratedDeriv_modelPhaseMorseWeight_eq hσ hδ hF₁ hv hz,
      iteratedDeriv_modelPhaseMorseAmplitude_formula hχ hσ hδ hF₁ hv hz]
    apply inversePhaseEval_abs_le
    exact fun j hj => morseWeightJet_abs_le hσ hδ hF hv hz hM n hP hb j hj
  · rw [iteratedDeriv_modelPhaseMorseWeight_zero hs hσ hδ hF₁ hv hz,abs_zero]
    exact morseWeightDerivativeBound_nonneg hσ hM n

theorem smoothCutoff_finite_jet_bound {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (Q : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ u ∈ Ioo (1 : ℝ) 2, ∀ k ≤ Q, |iteratedDeriv k χ u| ≤ M := by
  let B : ℝ → ℝ := fun u => ∑ k ∈ Finset.range (Q+1), |iteratedDeriv k χ u|
  have hB : Continuous B := continuous_finsetSum _ fun k _ =>
    (hχ.continuous_iteratedDeriv k (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).abs
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1 : ℝ) 2) hB.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro u hu k hk
  have hsum : |iteratedDeriv k χ u| ≤ B u :=
    Finset.single_le_sum (fun j _ => abs_nonneg (iteratedDeriv j χ u))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))
  exact hsum.trans ((le_abs_self _).trans
    ((hM u (Ioo_subset_Icc_self hu)).trans (le_max_left _ _)))

theorem modelPhaseMorseWeight_uniform_derivative
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ v : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      IsApproximateModelPhaseFunction F σ (morseWeightDerivativeOrder n) δ →
      v ∈ modelPhaseSlopeRange F →
      ∀ z : ℝ, |iteratedDeriv n (modelPhaseMorseWeight χ F v) z| ≤ C := by
  obtain ⟨M,hM,hb⟩ := smoothCutoff_finite_jet_bound hχ (morseWeightCutoffOrder n)
  refine ⟨max (morseWeightDerivativeBound σ M n) 1,le_max_right _ _,?_⟩
  intro F δ v hδ hF hv z
  exact (modelPhaseMorseWeight_iteratedDeriv_bound hχ hs hσ hδ hF hv
    (zero_le_one.trans hM) n le_rfl hb z).trans (le_max_left _ _)

end TaoTrudgianYang2025
