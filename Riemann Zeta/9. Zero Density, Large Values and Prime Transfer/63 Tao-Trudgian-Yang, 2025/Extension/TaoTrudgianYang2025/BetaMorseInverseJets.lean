import TaoTrudgianYang2025.BetaMorseJetBounds

/-!
# All-order derivatives of the actual inverse quadratic coordinate

The existing inverse-expression calculus is instantiated at the actual
quadratic inverse and derivatives of its coordinate. No derivative formula
or uniform inverse estimate is assumed.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def modelPhaseMorseInverseJet (F : ℝ → ℝ) (v z : ℝ) : ℕ → ℝ
  | 0 => modelPhaseMorseInverse F v z
  | 1 => (deriv (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z))⁻¹
  | n+2 => iteratedDeriv (n+1) (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z)

theorem modelPhaseMorseInverseJet_hasDerivAt
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (j : ℕ) :
    HasDerivAt (fun x => modelPhaseMorseInverseJet F v x j)
      (inversePhaseEval (inversePhaseAtomDerivative j) (modelPhaseMorseInverseJet F v z)) z := by
  have hi := (modelPhaseMorseInverse_hasStrictDerivAt hσ hδ hF hv hz).hasDerivAt
  have hu := modelPhaseMorseInverse_mem hz
  have hw := modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu
  match j with
  | 0 => exact hi
  | 1 =>
      have hc := (contDiffAt_iteratedDeriv_infty hw 1).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hne : iteratedDeriv 1 (modelPhaseMorseCoordinate F v) (modelPhaseMorseInverse F v z) ≠ 0 := by
        simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
          (modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv hu).ne'
      have hh := (hc.hasDerivAt.comp z hi).inv hne
      convert hh using 1
      · funext x
        simp only [modelPhaseMorseInverseJet,Pi.inv_apply,Function.comp_apply,
          iteratedDeriv_succ,iteratedDeriv_zero]
      · simp only [inversePhaseEval,inversePhaseAtomDerivative,modelPhaseMorseInverseJet,
          iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_apply,div_eq_mul_inv]
        ring
  | n+2 =>
      have hc := (contDiffAt_iteratedDeriv_infty hw (n+1)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert hc.hasDerivAt.comp z hi using 1
      simp only [inversePhaseEval,inversePhaseAtomDerivative,modelPhaseMorseInverseJet,
        iteratedDeriv_succ]

theorem morseInverseEval_hasDerivAt
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (modelPhaseMorseInverseJet F v x))
      (inversePhaseEval (inversePhaseDifferentiate e) (modelPhaseMorseInverseJet F v z)) z := by
  induction e with
  | scalar c => exact hasDerivAt_const z c
  | atom j => exact modelPhaseMorseInverseJet_hasDerivAt hσ hδ hF hv hz j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem iteratedDeriv_modelPhaseMorseInverse_formula
    {F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseInverse F v) z =
      inversePhaseEval (inversePhaseDerivativeExpression n) (modelPhaseMorseInverseJet F v z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (modelPhaseMorseInverse F v) =ᶠ[𝓝 z]
          (fun x => inversePhaseEval (inversePhaseDerivativeExpression n)
            (modelPhaseMorseInverseJet F v x)) := by
        filter_upwards [(modelPhaseMorseRange_isOpen hσ hδ hF hv).mem_nhds hz] with x hx
        exact ih hx
      rw [he.deriv_eq,
        (morseInverseEval_hasDerivAt hσ hδ hF hv hz (inversePhaseDerivativeExpression n)).deriv]
      rfl

end TaoTrudgianYang2025
