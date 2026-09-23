import TaoTrudgianYang2025.SargosQuarticMorseWeightJets

/-! Global all-order quartic weight bounds with the cutoff jet budget explicit.
The constants do not depend on either phase parameter. No uniform budget
is inferred for a varying family of cutoffs. -/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticMorseWeightCutoffOrder (n : ℕ) : ℕ :=
  inversePhaseOrder (morseWeightDerivativeExpression n)

def sargosQuarticMorseWeightJetBudget (M : ℝ) (n : ℕ) : ℝ :=
  M+∑ j ∈ Finset.range (sargosQuarticMorseWeightCutoffOrder n+2),
    sargosQuarticMorseInverseDerivativeBound j

def sargosQuarticMorseWeightDerivativeBound (M : ℝ) (n : ℕ) : ℝ :=
  inversePhaseMagnitude (morseWeightDerivativeExpression n) (sargosQuarticMorseWeightJetBudget M n)

theorem sargosQuarticMorseWeightDerivativeBound_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ sargosQuarticMorseWeightDerivativeBound M n :=
  inversePhaseMagnitude_nonneg _ (add_nonneg hM
    (Finset.sum_nonneg fun j _ => sargosQuarticMorseInverseDerivativeBound_nonneg j))

theorem sargosQuarticMorseWeightJet_abs_le {χ : ℝ → ℝ} {ε r z M : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r)
    (hM : 0 ≤ M) (n : ℕ)
    (hχ : ∀ u ∈ Ioo (0 : ℝ) 3, ∀ k ≤ sargosQuarticMorseWeightCutoffOrder n,
      |iteratedDeriv k χ u| ≤ M)
    (j : ℕ) (hj : j ≤ sargosQuarticMorseWeightCutoffOrder n) :
    |sargosQuarticMorseWeightJet χ ε r z j| ≤ sargosQuarticMorseWeightJetBudget M n := by
  unfold sargosQuarticMorseWeightJet
  have hsum : 0 ≤ ∑ k ∈ Finset.range (sargosQuarticMorseWeightCutoffOrder n+2),
      sargosQuarticMorseInverseDerivativeBound k :=
    Finset.sum_nonneg fun k _ => sargosQuarticMorseInverseDerivativeBound_nonneg k
  split_ifs
  · exact (hχ _ (sargosQuarticMorseInverse_mem hε hr hz) (j/2) (by omega)).trans
      (by unfold sargosQuarticMorseWeightJetBudget; linarith)
  · have hi := sargosQuarticMorseInverse_iteratedDeriv_bound hε hr hz (j/2+1)
    have hb := Finset.single_le_sum (f := sargosQuarticMorseInverseDerivativeBound)
      (s := Finset.range (sargosQuarticMorseWeightCutoffOrder n+2))
      (fun k _ => sargosQuarticMorseInverseDerivativeBound_nonneg k)
      (Finset.mem_range.mpr (by omega : j/2+1 < sargosQuarticMorseWeightCutoffOrder n+2))
    exact hi.trans (by unfold sargosQuarticMorseWeightJetBudget; linarith)

theorem sargosQuarticMorseWeight_iteratedDeriv_bound {χ : ℝ → ℝ} {ε r M : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hM : 0 ≤ M) (n : ℕ)
    (hb : ∀ u ∈ Ioo (0 : ℝ) 3, ∀ k ≤ sargosQuarticMorseWeightCutoffOrder n,
      |iteratedDeriv k χ u| ≤ M) (z : ℝ) :
    |iteratedDeriv n (sargosQuarticMorseWeight χ ε r) z| ≤
      sargosQuarticMorseWeightDerivativeBound M n := by
  by_cases hz : z ∈ sargosQuarticMorseRange ε r
  · rw [sargosQuarticMorseWeight_iteratedDeriv_eq hε hr hz,
      sargosQuarticMorseAmplitude_iteratedDeriv_formula hχ hε hr hz]
    apply inversePhaseEval_abs_le
    exact fun j hj => sargosQuarticMorseWeightJet_abs_le hε hr hz hM n hb j hj
  · rw [sargosQuarticMorseWeight_iteratedDeriv_zero hs hε hr hz,abs_zero]
    exact sargosQuarticMorseWeightDerivativeBound_nonneg hM n

end TaoTrudgianYang2025

