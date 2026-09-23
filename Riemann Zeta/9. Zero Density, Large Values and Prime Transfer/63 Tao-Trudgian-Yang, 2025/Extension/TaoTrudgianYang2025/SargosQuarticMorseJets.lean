import TaoTrudgianYang2025.SargosQuarticMorseCurvature

/-! Actual all-order derivative formulas for the quartic quadratic coordinate. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def sargosQuarticMorseJet (ε r u : ℝ) : ℕ → ℝ
  | 0 => u-r
  | 1 => Real.sqrt (sargosQuarticMorseCurvature ε r u)
  | 2 => (Real.sqrt (sargosQuarticMorseCurvature ε r u))⁻¹
  | n+3 => iteratedDeriv (n+1) (sargosQuarticMorseCurvature ε r) u

theorem sargosQuarticMorseJet_hasDerivAt {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Ioo 0 3) (j : ℕ) :
    HasDerivAt (fun x => sargosQuarticMorseJet ε r x j)
      (inversePhaseEval (morseAtomDerivative j) (sargosQuarticMorseJet ε r u)) u := by
  have hA := (sargosQuarticMorseCurvature_contDiff ε r).contDiffAt (x := u)
  have hb := (sargosQuarticMorseCoefficient_bounds hε hr ⟨hu.1.le,hu.2.le⟩).1
  have hp : 0 < sargosQuarticMorseCurvature ε r u := by
    unfold sargosQuarticMorseCurvature
    linarith
  have hd := (hA.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hq := hd.sqrt hp.ne'
  match j with
  | 0 => exact (hasDerivAt_id u).sub_const r
  | 1 =>
      convert hq using 1
      simp only [inversePhaseEval,morseAtomDerivative,sargosQuarticMorseJet,
        iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv,mul_inv_rev]
      ring
  | 2 =>
      convert hq.inv (Real.sqrt_pos.mpr hp).ne' using 1
      simp only [inversePhaseEval,morseAtomDerivative,sargosQuarticMorseJet,
        iteratedDeriv_succ,iteratedDeriv_zero,div_eq_mul_inv,mul_inv_rev]
      ring
  | n+3 =>
      have h := (contDiffAt_iteratedDeriv_infty hA (n+1)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert h.hasDerivAt using 1
      simp only [inversePhaseEval,morseAtomDerivative,sargosQuarticMorseJet,iteratedDeriv_succ]

theorem sargosQuarticMorseEval_hasDerivAt {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Ioo 0 3)
    (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (sargosQuarticMorseJet ε r x))
      (inversePhaseEval (morseDifferentiate e) (sargosQuarticMorseJet ε r u)) u := by
  induction e with
  | scalar c => exact hasDerivAt_const u c
  | atom j => exact sargosQuarticMorseJet_hasDerivAt hε hr hu j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem sargosQuarticMorseCoordinate_iteratedDeriv_formula {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Ioo 0 3) (n : ℕ) :
    iteratedDeriv n (sargosQuarticMorseCoordinate ε r) u =
      inversePhaseEval (morseDerivativeExpression n) (sargosQuarticMorseJet ε r u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (sargosQuarticMorseCoordinate ε r) =ᶠ[𝓝 u]
          (fun x => inversePhaseEval (morseDerivativeExpression n) (sargosQuarticMorseJet ε r x)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
        exact ih hx
      rw [he.deriv_eq,(sargosQuarticMorseEval_hasDerivAt hε hr hu (morseDerivativeExpression n)).deriv]
      rfl

end TaoTrudgianYang2025

