import TaoTrudgianYang2025.SargosQuarticMorseGlobalIntegral
import TaoTrudgianYang2025.BetaMorseWeightJets

/-! All-order derivatives of the actual transported quartic cutoff weight. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def sargosQuarticMorseWeightJet (χ : ℝ → ℝ) (ε r z : ℝ) (j : ℕ) : ℝ :=
  if j%2 = 0 then iteratedDeriv (j/2) χ (sargosQuarticMorseInverse ε r z)
  else iteratedDeriv (j/2+1) (sargosQuarticMorseInverse ε r) z

theorem sargosQuarticMorseWeightJet_hasDerivAt
    {χ : ℝ → ℝ} {ε r z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) (j : ℕ) :
    HasDerivAt (fun x => sargosQuarticMorseWeightJet χ ε r x j)
      (inversePhaseEval (morseWeightAtomDerivative j) (sargosQuarticMorseWeightJet χ ε r z)) z := by
  have hi := sargosQuarticMorseInverse_contDiffAt hε hr hz
  have hdiv : (j+2)/2 = j/2+1 := by omega
  by_cases hj : j%2 = 0
  · have hj' : (j+2)%2 = 0 := by omega
    have hc := (contDiffAt_iteratedDeriv_infty (u := sargosQuarticMorseInverse ε r z) hχ.contDiffAt (j/2)).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hd := (hi.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
    convert hc.hasDerivAt.comp z hd using 1
    · simp only [sargosQuarticMorseWeightJet,if_pos hj,Function.comp_def]
    · simp only [inversePhaseEval,morseWeightAtomDerivative,if_pos hj,sargosQuarticMorseWeightJet,
        if_pos hj',hdiv]
      norm_num [iteratedDeriv_succ]
  · have hj' : (j+2)%2 ≠ 0 := by omega
    have hc := (contDiffAt_iteratedDeriv_infty hi (j/2+1)).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    convert hc.hasDerivAt using 1
    · simp only [sargosQuarticMorseWeightJet,if_neg hj]
    · simp only [inversePhaseEval,morseWeightAtomDerivative,if_neg hj,sargosQuarticMorseWeightJet,
        if_neg hj',hdiv,iteratedDeriv_succ]

theorem sargosQuarticMorseWeightEval_hasDerivAt
    {χ : ℝ → ℝ} {ε r z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (sargosQuarticMorseWeightJet χ ε r x))
      (inversePhaseEval (morseWeightDifferentiate e) (sargosQuarticMorseWeightJet χ ε r z)) z := by
  induction e with
  | scalar c => exact hasDerivAt_const z c
  | atom j => exact sargosQuarticMorseWeightJet_hasDerivAt hχ hε hr hz j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem sargosQuarticMorseAmplitude_iteratedDeriv_formula
    {χ : ℝ → ℝ} {ε r z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) (n : ℕ) :
    iteratedDeriv n (sargosQuarticMorseAmplitude χ ε r) z =
      inversePhaseEval (morseWeightDerivativeExpression n) (sargosQuarticMorseWeightJet χ ε r z) := by
  induction n generalizing z with
  | zero =>
      simp [morseWeightDerivativeExpression,inversePhaseEval,sargosQuarticMorseWeightJet,
        sargosQuarticMorseAmplitude,iteratedDeriv_succ]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (sargosQuarticMorseAmplitude χ ε r) =ᶠ[𝓝 z]
          (fun x => inversePhaseEval (morseWeightDerivativeExpression n) (sargosQuarticMorseWeightJet χ ε r x)) := by
        filter_upwards [(sargosQuarticMorseRange_isOpen hε hr).mem_nhds hz] with x hx
        exact ih hx
      rw [he.deriv_eq,
        (sargosQuarticMorseWeightEval_hasDerivAt hχ hε hr hz (morseWeightDerivativeExpression n)).deriv]
      rfl

theorem sargosQuarticMorseWeight_iteratedDeriv_eq
    {χ : ℝ → ℝ} {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) (n : ℕ) :
    iteratedDeriv n (sargosQuarticMorseWeight χ ε r) z =
      iteratedDeriv n (sargosQuarticMorseAmplitude χ ε r) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [(sargosQuarticMorseRange_isOpen hε hr).mem_nhds hz] with x hx
  exact sargosQuarticMorseWeight_eq hx

theorem sargosQuarticMorseWeight_iteratedDeriv_zero
    {χ : ℝ → ℝ} {ε r z : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∉ sargosQuarticMorseRange ε r) (n : ℕ) :
    iteratedDeriv n (sargosQuarticMorseWeight χ ε r) z = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hz ((sargosQuarticMorseWeight_deriv_support hs hε hr n).trans (image_mono hs) h)

end TaoTrudgianYang2025


