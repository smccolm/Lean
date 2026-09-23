import TaoTrudgianYang2025.SargosQuarticMorseInverseJets

/-! Explicit parameter-independent bounds for every actual inverse-coordinate derivative. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticMorseInverseJetMagnitude : ℕ → ℝ
  | 0 => 3
  | 1 => 3
  | n+2 => sargosQuarticMorseDerivativeBound (n+1)

def sargosQuarticMorseInverseJetBudget (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), sargosQuarticMorseInverseJetMagnitude j

def sargosQuarticMorseInverseDerivativeBound (n : ℕ) : ℝ :=
  inversePhaseMagnitude (inversePhaseDerivativeExpression n)
    (sargosQuarticMorseInverseJetBudget (inversePhaseOrder (inversePhaseDerivativeExpression n)))

theorem sargosQuarticMorseInverseJetMagnitude_nonneg (j : ℕ) :
    0 ≤ sargosQuarticMorseInverseJetMagnitude j := by
  match j with
  | 0 => norm_num [sargosQuarticMorseInverseJetMagnitude]
  | 1 => norm_num [sargosQuarticMorseInverseJetMagnitude]
  | n+2 => exact sargosQuarticMorseDerivativeBound_nonneg (n+1)

theorem sargosQuarticMorseInverseJetMagnitude_le_budget {K j : ℕ} (hj : j ≤ K) :
    sargosQuarticMorseInverseJetMagnitude j ≤ sargosQuarticMorseInverseJetBudget K :=
  Finset.single_le_sum (fun k _ => sargosQuarticMorseInverseJetMagnitude_nonneg k)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

theorem sargosQuarticMorseInverseDerivativeBound_nonneg (n : ℕ) :
    0 ≤ sargosQuarticMorseInverseDerivativeBound n :=
  inversePhaseMagnitude_nonneg _
    (Finset.sum_nonneg fun j _ => sargosQuarticMorseInverseJetMagnitude_nonneg j)

theorem sargosQuarticMorseInverseJet_abs_le {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) (j : ℕ) :
    |sargosQuarticMorseInverseJet ε r z j| ≤ sargosQuarticMorseInverseJetMagnitude j := by
  have hu := sargosQuarticMorseInverse_mem hε hr hz
  match j with
  | 0 =>
      change |sargosQuarticMorseInverse ε r z| ≤ 3
      rw [abs_of_pos hu.1]
      exact hu.2.le
  | 1 =>
      change |(deriv (sargosQuarticMorseCoordinate ε r)
        (sargosQuarticMorseInverse ε r z))⁻¹| ≤ 3
      rw [← (sargosQuarticMorseInverse_hasStrictDerivAt hε hr hz).hasDerivAt.deriv]
      have hb := sargosQuarticMorseInverse_deriv_bounds hε hr hz
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2]
  | n+2 =>
      exact sargosQuarticMorseCoordinate_iteratedDeriv_bound hε hr hu (n+1)

theorem sargosQuarticMorseInverse_iteratedDeriv_bound {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) (n : ℕ) :
    |iteratedDeriv n (sargosQuarticMorseInverse ε r) z| ≤
      sargosQuarticMorseInverseDerivativeBound n := by
  rw [sargosQuarticMorseInverse_iteratedDeriv_formula hε hr hz n]
  apply inversePhaseEval_abs_le
  intro j hj
  exact (sargosQuarticMorseInverseJet_abs_le hε hr hz j).trans
    (sargosQuarticMorseInverseJetMagnitude_le_budget hj)

end TaoTrudgianYang2025

