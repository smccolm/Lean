import Dubon2026.RankinSelbergEnergyConsequences
import Dubon2026.CuspConditionalConcentration

/-! # Bridging the literal asymptotic Rankin–Selberg input to the proved energy deductions

The estimate itself remains an explicit upstream input for genuine cusp forms.
-/

namespace Dubon2026

open Filter Set MeasureTheory Asymptotics
open scoped Topology

noncomputable section

theorem squareSummatory_nonneg (a : ℕ → ℂ) (x : ℝ) : 0 ≤ squareSummatory a x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem squareSummatory_mono (a : ℕ → ℂ) : Monotone (squareSummatory a) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy)
  · intro n _ _
    exact sq_nonneg _

/-- Enlarge the eventual O-constant using the actual finite initial square sum. -/
theorem uniform_rankin_selberg_remainder {a : ℕ → ℂ} {c : ℝ}
    (hRS : (fun x : ℝ => squareSummatory a x - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |squareSummatory a x - c * x| ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C₀, hC₀, hbound⟩ := hRS.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp hbound.bound
  obtain ⟨M, hM⟩ := exists_nat_ge (max T 1)
  have hMT : T ≤ (M : ℝ) := (le_max_left T 1).trans hM
  let D := squareSummatory a M + |c| * M
  let C := max C₀ D
  have hC : 0 ≤ C := hC₀.le.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hp : 0 ≤ x ^ (3 / 5 : ℝ) := Real.rpow_nonneg hx0 _
  by_cases hxM : (M : ℝ) ≤ x
  · have hb := hT x (hMT.trans hxM)
    simp only [Real.norm_eq_abs, abs_of_nonneg hp] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  · have hs : |squareSummatory a x - c * x| ≤ D := by
      have ha := squareSummatory_mono a (le_of_not_ge hxM)
      have hb := abs_sub (squareSummatory a x) (c * x)
      rw [abs_of_nonneg (squareSummatory_nonneg a x), abs_mul, abs_of_nonneg hx0] at hb
      have hc := mul_le_mul_of_nonneg_left (le_of_not_ge hxM) (abs_nonneg c)
      dsimp only [D]
      linarith
    have hr : 1 ≤ x ^ (3 / 5 : ℝ) := Real.one_le_rpow hx (by norm_num)
    exact (hs.trans (le_max_right _ _)).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hC)

/-- Literal asymptotic notation yields the unweighted mean needed by the cusp consumer. -/
theorem mean_square_limit_of_rankin_selberg {a : ℕ → ℂ} {c : ℝ}
    (hRS : (fun x : ℝ => squareSummatory a x - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N) atTop (𝓝 c) := by
  obtain ⟨C, _, hC⟩ := uniform_rankin_selberg_remainder hRS
  exact mean_square_limit_of_remainder (by norm_num) hC

/-- All three exact weighted conclusions from the paper's literal asymptotic input. -/
theorem rankin_selberg_weighted_energy_of_bigO {a : ℕ → ℂ} {c : ℝ}
    (hRS : (fun x : ℝ => squareSummatory a x - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ))) :
    (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ => (coefficientEnergy a N σ -
      c * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      |coefficientEnergy a N (1 / 2) - c * Real.log N| ≤ B) ∧
    (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      0 ≤ coefficientEnergy a N σ ∧ coefficientEnergy a N σ ≤ B) := by
  obtain ⟨C, hC, he⟩ := uniform_rankin_selberg_remainder hRS
  exact rankin_selberg_weighted_energy hC he

open UpperHalfPlane ModularForm CongruenceSubgroup in
open scoped MatrixGroups CongruenceSubgroup in
/-- Actual cusp coefficients consume the asymptotic mean-square input and selected-prime density.
The arithmetic theorems themselves are still hypotheses, not asserted proofs. -/
theorem cusp_concentration_of_rankin_selberg_prime_density {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : (qExpansion 1 f).coeff 1 = 1) {c density : ℝ}
    (hRS : (fun x : ℝ => squareSummatory (normalizedCuspCoefficients f) x - c * x) =O[atTop]
      (fun x : ℝ => x ^ (3 / 5 : ℝ)))
    (hdensity : 0 < density)
    (hd : Tendsto (fun N : ℕ => ((selectedPrimesUpTo (cuspPrimeSelection f) N).card : ℝ) /
      Nat.primeCounting N) atTop (𝓝 density)) :
    TendstoLocallyUniformly (normalizedJessen (normalizedCuspCoefficients f))
      (fun σ => max (1 / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (normalizedCuspCoefficients_one f hf)) atTop
      (𝓝 (⟨Measure.dirac (1 / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    TendstoLocallyUniformly (normalizedJessen (cuspCoefficients f))
      (fun σ => max ((k : ℝ) / 2 - σ) 0) atTop ∧
    Tendsto (jessenProbability (a := cuspCoefficients f) hf) atTop
      (𝓝 (⟨Measure.dirac ((k : ℝ) / 2), inferInstance⟩ : ProbabilityMeasure ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, ∃ hN : 1 ≤ N, 1 < lastIndex (cuspCoefficients f) N ∧ ∀ l u : ℝ,
      Tendsto (fun T : ℝ => (2 * Real.pi / Real.log (lastIndex (cuspCoefficients f) N)) *
        ((verticalZeroCount (cuspCoefficients f) N hN (hf.trans_ne one_ne_zero) l u T : ℝ) /
          (2 * T))) atTop
        (𝓝 (((jessenProbability (a := cuspCoefficients f) hf N : Measure ℝ) (Ioo l u)).toReal))) :=
  cusp_concentration_of_mean_prime_density f hf
    (mean_square_limit_of_rankin_selberg hRS) hdensity hd

end

end Dubon2026
