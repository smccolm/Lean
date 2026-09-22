import TaoTrudgianYang2025.BetaInverseExpressions

/-!
# Actual inverse and Legendre derivatives of every order

The finite expressions are interpreted at the genuine inverse derivative.
Their recurrence is proved by the chain, product and reciprocal rules,
then consumed by the literal iteratedDeriv operators.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

def modelPhaseInverseJet (F : ℝ → ℝ) (v : ℝ) : ℕ → ℝ
  | 0 => modelPhaseInverseSlope F v
  | 1 => (deriv (deriv F) (modelPhaseInverseSlope F v))⁻¹
  | n+2 => iteratedDeriv (n+2) F (modelPhaseInverseSlope F v)

theorem contDiffAt_iteratedDeriv_infty {F : ℝ → ℝ} {u : ℝ}
    (hF : ContDiffAt ℝ ∞ F u) (n : ℕ) :
    ContDiffAt ℝ ∞ (iteratedDeriv n F) u := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact hn.derivWithin (by simp)

theorem approximateModelPhase_iteratedDeriv_contDiffAt
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (n : ℕ) :
    ContDiffAt ℝ ∞ (iteratedDeriv n F) u := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using approximateModelPhase_contDiffAt hF hu
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact hn.derivWithin (by simp)

theorem modelPhaseInverseJet_hasDerivAt
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (j : ℕ) :
    HasDerivAt (fun w => modelPhaseInverseJet F w j)
      (inversePhaseEval (inversePhaseAtomDerivative j) (modelPhaseInverseJet F v)) v := by
  have hi := (modelPhaseInverseSlope_hasStrictDerivAt hσ hδ hF hv).hasDerivAt
  have hu := modelPhaseInverseSlope_mem hv
  match j with
  | 0 => exact hi
  | 1 =>
      have hc := (approximateModelPhase_iteratedDeriv_contDiffAt hF hu 2).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hne : iteratedDeriv 2 F (modelPhaseInverseSlope F v) ≠ 0 := by
        simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
          approximateModelPhase_secondDeriv_ne_zero hσ hδ hF hu
      have hh := (hc.hasDerivAt.comp v hi).inv hne
      convert hh using 1
      · funext w
        simp only [modelPhaseInverseJet, Pi.inv_apply, Function.comp_apply,
          iteratedDeriv_succ, iteratedDeriv_zero]
      · simp only [inversePhaseEval, inversePhaseAtomDerivative, modelPhaseInverseJet,
          iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply, div_eq_mul_inv]
        ring
  | n+2 =>
      have hc := (approximateModelPhase_iteratedDeriv_contDiffAt hF hu (n+2)).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert hc.hasDerivAt.comp v hi using 1
      simp only [inversePhaseEval, inversePhaseAtomDerivative, modelPhaseInverseJet,
        iteratedDeriv_succ]

theorem inversePhaseEval_modelPhaseInverseJet_hasDerivAt
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (e : InversePhaseExpression) :
    HasDerivAt (fun w => inversePhaseEval e (modelPhaseInverseJet F w))
      (inversePhaseEval (inversePhaseDifferentiate e) (modelPhaseInverseJet F v)) v := by
  induction e with
  | scalar c => exact hasDerivAt_const v c
  | atom j => exact modelPhaseInverseJet_hasDerivAt hσ hδ hF hv j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem iteratedDeriv_modelPhaseInverseSlope_formula
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (n : ℕ) :
    iteratedDeriv n (modelPhaseInverseSlope F) v =
      inversePhaseEval (inversePhaseDerivativeExpression n) (modelPhaseInverseJet F v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n hn =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (modelPhaseInverseSlope F) =ᶠ[𝓝 v]
          (fun w => inversePhaseEval (inversePhaseDerivativeExpression n)
            (modelPhaseInverseJet F w)) := by
        filter_upwards [(modelPhaseSlopeRange_isOpen hσ hδ hF).mem_nhds hv] with w hw
        exact hn hw
      rw [he.deriv_eq,
        (inversePhaseEval_modelPhaseInverseJet_hasDerivAt hσ hδ hF hv
          (inversePhaseDerivativeExpression n)).deriv]
      rfl

theorem iteratedDeriv_modelPhaseLegendreDual_formula
    {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) (n : ℕ) :
    iteratedDeriv (n+1) (modelPhaseLegendreDual F) v =
      inversePhaseEval (inversePhaseDerivativeExpression n) (modelPhaseInverseJet F v) := by
  have he : deriv (modelPhaseLegendreDual F) =ᶠ[𝓝 v] modelPhaseInverseSlope F := by
    filter_upwards [(modelPhaseSlopeRange_isOpen hσ hδ hF).mem_nhds hv] with w hw
    exact deriv_modelPhaseLegendreDual hσ hδ hF hw
  rw [iteratedDeriv_succ', he.iteratedDeriv_eq n]
  exact iteratedDeriv_modelPhaseInverseSlope_formula hσ hδ hF hv n

end TaoTrudgianYang2025
