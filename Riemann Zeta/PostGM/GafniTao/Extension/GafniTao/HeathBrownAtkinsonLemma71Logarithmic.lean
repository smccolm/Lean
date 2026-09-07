import GafniTao.HeathBrownAtkinsonLemma71FirstMoment
import GafniTao.HeathBrownDivisorSquare

/-!
# Logarithmic coefficient insertion in Heath--Brown's Lemma 7.1

This file inserts the proved divisor-square mean into the three-radical
source estimate.  It deliberately retains the exact Atkinson coefficients,
the scaled harmonic factor, and all three terms.  The subsequent physical
scale lemma may simplify these quantities, but no asymptotic loss is hidden
in this step.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The explicit logarithmic upper bound for the Atkinson coefficient
energy on `(K,2K]`. -/
def heathBrownAtkinsonLogEnergy (K : ℕ) : ℝ :=
  ((2 * K : ℕ) : ℝ) * (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ)

/-- The three source radicals after inserting the logarithmic
divisor-square estimate. -/
def heathBrownAtkinsonLemma71LogMajorant
    (T G J : ℝ) (K R : ℕ) : ℝ :=
  Real.sqrt
      (heathBrownAtkinsonLogEnergy K * (R : ℝ) * (K : ℝ)) +
    Real.sqrt
      (heathBrownAtkinsonLogEnergy K * (R : ℝ) *
        ((R : ℝ) * heathBrownAtkinsonSourceFirstCoefficient T J K)) +
    Real.sqrt
      (heathBrownAtkinsonLogEnergy K * (R : ℝ) *
        heathBrownAtkinsonSourceReciprocalContribution T G J K)

theorem heathBrownAtkinsonEnergy_le_logEnergy
    {K : ℕ} (hK : 1 ≤ K) :
    heathBrownAtkinsonEnergy K ≤ heathBrownAtkinsonLogEnergy K := by
  unfold heathBrownAtkinsonEnergy heathBrownAtkinsonLogEnergy
  exact sum_Ioc_heathBrownDivisorCoefficient_sq_le_log_cube hK

/-- Source-shaped Lemma 7.1 with the coefficient energy replaced by its
proved logarithmic upper bound, uniformly in every prefix. -/
theorem heathBrownAtkinson_lemma71_source_logarithmic
    {K j : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 1 ≤ K)
    (hj : j ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖) ≤
      heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by
  have hbase := heathBrownAtkinson_lemma71_source_firstMoment
    hT hG (Nat.zero_lt_of_lt hK) hj hblock hSep hRange hDiameter
  have henergy := heathBrownAtkinsonEnergy_le_logEnergy hK
  have hR : 0 ≤ (W.card : ℝ) := by positivity
  have hKR : 0 ≤ (K : ℝ) := by positivity
  have hfirst : 0 ≤ heathBrownAtkinsonSourceFirstCoefficient T J K :=
    heathBrownAtkinsonSourceFirstCoefficient_nonneg hT
  have hrec :
      0 ≤ heathBrownAtkinsonSourceReciprocalContribution T G J K := by
    unfold heathBrownAtkinsonSourceReciprocalContribution
    have hhQ : 0 ≤ harmonic ⌈J / G⌉₊ := by
      rw [harmonic_eq_sum_Icc]
      positivity
    have hh : 0 ≤ (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) := by
      exact_mod_cast hhQ
    exact mul_nonneg
      (heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg hT)
      (mul_nonneg (div_nonneg (by norm_num) hG.le) hh)
  calc
    _ ≤ heathBrownAtkinsonLemma71FirstMomentMajorant T G J K W.card := hbase
    _ ≤ heathBrownAtkinsonLemma71LogMajorant T G J K W.card := by
      unfold heathBrownAtkinsonLemma71FirstMomentMajorant
        heathBrownAtkinsonLemma71LogMajorant
      gcongr


end

end GafniTao
