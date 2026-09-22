import TaoTrudgianYang2025.BetaMorseInverseJetBounds
import TaoTrudgianYang2025.BetaMorseGlobalIntegral

/-!
# Actual transformed-weight derivatives of every order

Even jet coordinates are original cutoff derivatives at the inverse point;
odd coordinates are derivatives of the actual inverse. The finite product
and chain calculus is proved against these functions before use in bounds.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def morseWeightJet (χ F : ℝ → ℝ) (v z : ℝ) (j : ℕ) : ℝ :=
  if j%2 = 0 then iteratedDeriv (j/2) χ (modelPhaseMorseInverse F v z)
  else iteratedDeriv (j/2+1) (modelPhaseMorseInverse F v) z

def morseWeightAtomDerivative (j : ℕ) : InversePhaseExpression :=
  if j%2 = 0 then .mul (.atom (j+2)) (.atom 1) else .atom (j+2)

def morseWeightDifferentiate : InversePhaseExpression → InversePhaseExpression
  | .scalar _ => .scalar 0
  | .atom j => morseWeightAtomDerivative j
  | .add e f => .add (morseWeightDifferentiate e) (morseWeightDifferentiate f)
  | .mul e f => .add (.mul (morseWeightDifferentiate e) f)
      (.mul e (morseWeightDifferentiate f))

def morseWeightDerivativeExpression : ℕ → InversePhaseExpression
  | 0 => .mul (.atom 0) (.atom 1)
  | n+1 => morseWeightDifferentiate (morseWeightDerivativeExpression n)

theorem morseWeightJet_hasDerivAt
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (j : ℕ) :
    HasDerivAt (fun x => morseWeightJet χ F v x j)
      (inversePhaseEval (morseWeightAtomDerivative j) (morseWeightJet χ F v z)) z := by
  have hi := modelPhaseMorseInverse_contDiffAt hσ hδ hF hv hz
  have hdiv : (j+2)/2 = j/2+1 := by omega
  by_cases hj : j%2 = 0
  · have hj' : (j+2)%2 = 0 := by omega
    have hc := (contDiffAt_iteratedDeriv_infty (u := modelPhaseMorseInverse F v z) hχ.contDiffAt (j/2)).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hd := (hi.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
    convert hc.hasDerivAt.comp z hd using 1
    · simp only [morseWeightJet,if_pos hj,Function.comp_def]
    · simp only [inversePhaseEval,morseWeightAtomDerivative,if_pos hj,morseWeightJet,
        if_pos hj',hdiv]
      norm_num [iteratedDeriv_succ]
  · have hj' : (j+2)%2 ≠ 0 := by omega
    have hc := (contDiffAt_iteratedDeriv_infty hi (j/2+1)).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    convert hc.hasDerivAt using 1
    · simp only [morseWeightJet,if_neg hj]
    · simp only [inversePhaseEval,morseWeightAtomDerivative,if_neg hj,morseWeightJet,
        if_neg hj',hdiv,iteratedDeriv_succ]

theorem morseWeightEval_hasDerivAt
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (morseWeightJet χ F v x))
      (inversePhaseEval (morseWeightDifferentiate e) (morseWeightJet χ F v z)) z := by
  induction e with
  | scalar c => exact hasDerivAt_const z c
  | atom j => exact morseWeightJet_hasDerivAt hχ hσ hδ hF hv hz j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem iteratedDeriv_modelPhaseMorseAmplitude_formula
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseAmplitude χ F v) z =
      inversePhaseEval (morseWeightDerivativeExpression n) (morseWeightJet χ F v z) := by
  induction n generalizing z with
  | zero =>
      simp [morseWeightDerivativeExpression,inversePhaseEval,morseWeightJet,
        modelPhaseMorseAmplitude,iteratedDeriv_succ]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (modelPhaseMorseAmplitude χ F v) =ᶠ[𝓝 z]
          (fun x => inversePhaseEval (morseWeightDerivativeExpression n) (morseWeightJet χ F v x)) := by
        filter_upwards [(modelPhaseMorseRange_isOpen hσ hδ hF hv).mem_nhds hz] with x hx
        exact ih hx
      rw [he.deriv_eq,
        (morseWeightEval_hasDerivAt hχ hσ hδ hF hv hz (morseWeightDerivativeExpression n)).deriv]
      rfl

theorem iteratedDeriv_modelPhaseMorseWeight_eq
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight χ F v) z =
      iteratedDeriv n (modelPhaseMorseAmplitude χ F v) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [(modelPhaseMorseRange_isOpen hσ hδ hF hv).mem_nhds hz] with x hx
  exact modelPhaseMorseWeight_eq hx

theorem iteratedDeriv_modelPhaseMorseWeight_zero
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∉ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseWeight χ F v) z = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hz ((modelPhaseMorseWeight_deriv_support hs hσ hδ hF hv n).trans (image_mono hs) h)

end TaoTrudgianYang2025
