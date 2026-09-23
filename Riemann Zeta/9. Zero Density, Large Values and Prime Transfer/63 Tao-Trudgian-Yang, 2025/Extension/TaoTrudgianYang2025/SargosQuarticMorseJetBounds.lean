import TaoTrudgianYang2025.SargosQuarticMorseJets

/-! Uniform coordinate-jet bounds, independent of the quartic parameters. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

def sargosQuarticMorseDerivativeBound (n : ℕ) : ℝ :=
  inversePhaseMagnitude (morseDerivativeExpression n) 3

theorem sargosQuarticMorseDerivativeBound_nonneg (n : ℕ) :
    0 ≤ sargosQuarticMorseDerivativeBound n :=
  inversePhaseMagnitude_nonneg _ (by norm_num)

theorem sargosQuarticMorseCurvature_derivative_bound {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3)
    (j : ℕ) (hj : 1 ≤ j) :
    |iteratedDeriv j (sargosQuarticMorseCurvature ε r) u| ≤ 3 := by
  match j with
  | 0 => omega
  | 1 =>
      rw [iteratedDeriv_one,sargosQuarticMorseCurvature_deriv]
      simp only [abs_mul,show |(4 : ℝ)| = 4 by norm_num]
      rw [abs_of_nonneg (add_nonneg hu.1 hr.1)]
      have h := mul_le_mul hε (show u+r ≤ 6 by linarith [hu.2,hr.2])
        (add_nonneg hu.1 hr.1) (by norm_num : (0 : ℝ) ≤ 1/96)
      nlinarith
  | 2 =>
      change |iteratedDeriv (1+1) (sargosQuarticMorseCurvature ε r) u| ≤ 3
      rw [iteratedDeriv_succ',
        sargosQuarticMorseCurvature_deriv,iteratedDeriv_one,
        sargosQuarticMorseCurvature_deriv_two]
      simp only [abs_mul,show |(4 : ℝ)| = 4 by norm_num]
      linarith
  | n+3 =>
      rw [sargosQuarticMorseCurvature_high_deriv]
      norm_num

theorem sargosQuarticMorseJet_abs_le {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) (j : ℕ) :
    |sargosQuarticMorseJet ε r u j| ≤ 3 := by
  have hs := sargosQuarticMorseCoordinate_sqrt_bounds hε hr hu
  match j with
  | 0 =>
      change |u-r| ≤ 3
      rw [abs_le]
      constructor <;> linarith [hu.1,hu.2,hr.1,hr.2]
  | 1 =>
      change |Real.sqrt (2*sargosQuarticMorseCoefficient ε r u)| ≤ 3
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      linarith [hs.2]
  | 2 =>
      change |(Real.sqrt (2*sargosQuarticMorseCoefficient ε r u))⁻¹| ≤ 3
      rw [abs_inv,abs_of_nonneg (Real.sqrt_nonneg _),← one_div]
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hs.1)).mpr
      linarith [hs.1]
  | n+3 =>
      exact sargosQuarticMorseCurvature_derivative_bound hε hr hu (n+1) (by omega)

theorem sargosQuarticMorseCoordinate_iteratedDeriv_bound {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Ioo 0 3) (n : ℕ) :
    |iteratedDeriv n (sargosQuarticMorseCoordinate ε r) u| ≤
      sargosQuarticMorseDerivativeBound n := by
  rw [sargosQuarticMorseCoordinate_iteratedDeriv_formula hε hr hu n]
  apply inversePhaseEval_abs_le
  intro j _
  exact sargosQuarticMorseJet_abs_le hε hr ⟨hu.1.le,hu.2.le⟩ j

end TaoTrudgianYang2025
