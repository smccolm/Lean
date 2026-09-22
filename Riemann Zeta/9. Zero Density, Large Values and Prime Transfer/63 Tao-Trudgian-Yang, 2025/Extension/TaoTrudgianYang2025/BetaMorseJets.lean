import TaoTrudgianYang2025.BetaTaylorJets
import TaoTrudgianYang2025.BetaInverseExpressions

/-!
# All-order formulas for the actual quadratic coordinate

The finite expression language is evaluated on displacement, square-root
averaged curvature, its reciprocal, and the actual curvature derivatives.
The differentiation rule is proved from these analytic objects.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def modelPhaseMorseJet (F : ℝ → ℝ) (v u : ℝ) : ℕ → ℝ
  | 0 => u-modelPhaseInverseSlope F v
  | 1 => Real.sqrt (modelPhaseAveragedCurvature F v u)
  | 2 => (Real.sqrt (modelPhaseAveragedCurvature F v u))⁻¹
  | n+3 => iteratedDeriv (n+1) (modelPhaseAveragedCurvature F v) u

def morseAtomDerivative : ℕ → InversePhaseExpression
  | 0 => .scalar 1
  | 1 => .mul (.scalar (1/2)) (.mul (.atom 2) (.atom 3))
  | 2 => .mul (.scalar (-1/2))
      (.mul (.atom 2) (.mul (.atom 2) (.mul (.atom 2) (.atom 3))))
  | n+3 => .atom (n+4)

def morseDifferentiate : InversePhaseExpression → InversePhaseExpression
  | .scalar _ => .scalar 0
  | .atom j => morseAtomDerivative j
  | .add e f => .add (morseDifferentiate e) (morseDifferentiate f)
  | .mul e f => .add (.mul (morseDifferentiate e) f)
      (.mul e (morseDifferentiate f))

def morseDerivativeExpression : ℕ → InversePhaseExpression
  | 0 => .mul (.atom 0) (.atom 1)
  | n+1 => morseDifferentiate (morseDerivativeExpression n)

theorem modelPhaseMorseJet_hasDerivAt
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) (j : ℕ) :
    HasDerivAt (fun x => modelPhaseMorseJet F v x j)
      (inversePhaseEval (morseAtomDerivative j) (modelPhaseMorseJet F v u)) u := by
  have hA := modelPhaseAveragedCurvature_contDiffAt hF hv hu
  have hp := modelPhaseAveragedCurvature_pos hσ hδ hF hv hu
  have hd := (hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hq := hd.sqrt hp.ne'
  match j with
  | 0 => exact (hasDerivAt_id u).sub_const _
  | 1 =>
      convert hq using 1
      simp only [inversePhaseEval,morseAtomDerivative,modelPhaseMorseJet,
        iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv,mul_inv_rev]
      ring
  | 2 =>
      convert hq.inv (Real.sqrt_pos.mpr hp).ne' using 1
      simp only [inversePhaseEval,morseAtomDerivative,modelPhaseMorseJet,
        iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv,mul_inv_rev]
      ring
  | n+3 =>
      have h := (contDiffAt_iteratedDeriv_infty hA (n+1)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert h.hasDerivAt using 1
      simp only [inversePhaseEval,morseAtomDerivative,modelPhaseMorseJet,iteratedDeriv_succ]

theorem morseEval_hasDerivAt
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (modelPhaseMorseJet F v x))
      (inversePhaseEval (morseDifferentiate e) (modelPhaseMorseJet F v u)) u := by
  induction e with
  | scalar c => exact hasDerivAt_const u c
  | atom j => exact modelPhaseMorseJet_hasDerivAt hσ hδ hF hv hu j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem iteratedDeriv_modelPhaseMorseCoordinate_formula
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) (n : ℕ) :
    iteratedDeriv n (modelPhaseMorseCoordinate F v) u =
      inversePhaseEval (morseDerivativeExpression n) (modelPhaseMorseJet F v u) := by
  induction n generalizing u with
  | zero =>
      exact modelPhaseMorseCoordinate_eq_smooth hF hv hu
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (modelPhaseMorseCoordinate F v) =ᶠ[𝓝 u]
          (fun x => inversePhaseEval (morseDerivativeExpression n) (modelPhaseMorseJet F v x)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
        exact ih hx
      rw [he.deriv_eq,(morseEval_hasDerivAt hσ hδ hF hv hu (morseDerivativeExpression n)).deriv]
      rfl

end TaoTrudgianYang2025
