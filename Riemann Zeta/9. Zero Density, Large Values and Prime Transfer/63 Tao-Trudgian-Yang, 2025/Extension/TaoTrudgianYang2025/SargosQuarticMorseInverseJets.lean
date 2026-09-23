import TaoTrudgianYang2025.SargosQuarticMorseJetBounds

/-! All-order formulas for the actual inverse quartic quadratic coordinate. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def sargosQuarticMorseInverseJet (ε r z : ℝ) : ℕ → ℝ
  | 0 => sargosQuarticMorseInverse ε r z
  | 1 => (deriv (sargosQuarticMorseCoordinate ε r) (sargosQuarticMorseInverse ε r z))⁻¹
  | n+2 => iteratedDeriv (n+1) (sargosQuarticMorseCoordinate ε r) (sargosQuarticMorseInverse ε r z)

theorem sargosQuarticMorseInverseJet_hasDerivAt {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) (j : ℕ) :
    HasDerivAt (fun x => sargosQuarticMorseInverseJet ε r x j)
      (inversePhaseEval (inversePhaseAtomDerivative j) (sargosQuarticMorseInverseJet ε r z)) z := by
  have hi := (sargosQuarticMorseInverse_hasStrictDerivAt hε hr hz).hasDerivAt
  have hu := sargosQuarticMorseInverse_mem hε hr hz
  have huc : sargosQuarticMorseInverse ε r z ∈ Icc 0 3 := ⟨hu.1.le,hu.2.le⟩
  have hp := (sargosQuarticMorseCoefficient_bounds hε hr huc).1
  have hw := sargosQuarticMorseCoordinate_contDiffAt
    (by linarith : 0 < sargosQuarticMorseCoefficient ε r (sargosQuarticMorseInverse ε r z))
  match j with
  | 0 => exact hi
  | 1 =>
      have hc := (contDiffAt_iteratedDeriv_infty hw 1).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hne : iteratedDeriv 1 (sargosQuarticMorseCoordinate ε r)
          (sargosQuarticMorseInverse ε r z) ≠ 0 := by
        rw [iteratedDeriv_one]
        have hb := (sargosQuarticMorseCoordinate_deriv_bounds hε hr huc).1
        linarith
      have hh := (hc.hasDerivAt.comp z hi).inv hne
      convert hh using 1
      · funext x
        simp only [sargosQuarticMorseInverseJet,Pi.inv_apply,Function.comp_apply,
          iteratedDeriv_succ,iteratedDeriv_zero]
      · simp only [inversePhaseEval,inversePhaseAtomDerivative,sargosQuarticMorseInverseJet,
          iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_apply,div_eq_mul_inv]
        ring
  | n+2 =>
      have hc := (contDiffAt_iteratedDeriv_infty hw (n+1)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      convert hc.hasDerivAt.comp z hi using 1
      simp only [inversePhaseEval,inversePhaseAtomDerivative,sargosQuarticMorseInverseJet,
        iteratedDeriv_succ]

theorem sargosQuarticMorseInverseEval_hasDerivAt {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) (e : InversePhaseExpression) :
    HasDerivAt (fun x => inversePhaseEval e (sargosQuarticMorseInverseJet ε r x))
      (inversePhaseEval (inversePhaseDifferentiate e) (sargosQuarticMorseInverseJet ε r z)) z := by
  induction e with
  | scalar c => exact hasDerivAt_const z c
  | atom j => exact sargosQuarticMorseInverseJet_hasDerivAt hε hr hz j
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem sargosQuarticMorseInverse_iteratedDeriv_formula {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) (n : ℕ) :
    iteratedDeriv n (sargosQuarticMorseInverse ε r) z =
      inversePhaseEval (inversePhaseDerivativeExpression n) (sargosQuarticMorseInverseJet ε r z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (sargosQuarticMorseInverse ε r) =ᶠ[𝓝 z]
          (fun x => inversePhaseEval (inversePhaseDerivativeExpression n)
            (sargosQuarticMorseInverseJet ε r x)) := by
        filter_upwards [(sargosQuarticMorseRange_isOpen hε hr).mem_nhds hz] with x hx
        exact ih hx
      rw [he.deriv_eq,
        (sargosQuarticMorseInverseEval_hasDerivAt hε hr hz (inversePhaseDerivativeExpression n)).deriv]
      rfl

end TaoTrudgianYang2025

