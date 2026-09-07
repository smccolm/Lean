import GafniTao.HeathBrownAtkinsonLemma71Source

/-!
# First-moment form of Ivić Lemma 7.1

This file takes the square root of the aggregate Gram inequality and keeps
the diagonal, reciprocal-gap, and exponent-pair terms as three separately
auditable radicals.  Subsequent scale algebra may enlarge these radicals to
Ivić's displayed monomials, but no term is discarded here.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The complete reciprocal-gap contribution in one source Gram row. -/
def heathBrownAtkinsonSourceReciprocalContribution
    (T G J : ℝ) (K : ℕ) : ℝ :=
  heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
    ((2 / G) * (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)))

/-- The exact three-radical majorant obtained from the source Gram row. -/
def heathBrownAtkinsonLemma71FirstMomentMajorant
    (T G J : ℝ) (K R : ℕ) : ℝ :=
  Real.sqrt
      (heathBrownAtkinsonEnergy K * (R : ℝ) * (K : ℝ)) +
    Real.sqrt
      (heathBrownAtkinsonEnergy K * (R : ℝ) *
        ((R : ℝ) * heathBrownAtkinsonSourceFirstCoefficient T J K)) +
    Real.sqrt
      (heathBrownAtkinsonEnergy K * (R : ℝ) *
        heathBrownAtkinsonSourceReciprocalContribution T G J K)

private theorem sqrt_three_sum_le
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤
      Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  calc
    Real.sqrt (a + b + c) = Real.sqrt ((a + b) + c) := by ring
    _ ≤ Real.sqrt (a + b) + Real.sqrt c :=
      sqrt_add_le_add_sqrt (add_nonneg ha hb) hc
    _ ≤ (Real.sqrt a + Real.sqrt b) + Real.sqrt c := by
      gcongr
      exact sqrt_add_le_add_sqrt ha hb
    _ = _ := by ring

/-- Source-shaped aggregate first-moment estimate, uniform in every prefix.
This is the precise replacement for the invalid per-ordinate prefix
selection route. -/
theorem heathBrownAtkinson_lemma71_source_firstMoment
    {K j : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 0 < K)
    (hj : j ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖) ≤
      heathBrownAtkinsonLemma71FirstMomentMajorant T G J K W.card := by
  let a : ℝ := heathBrownAtkinsonEnergy K * (W.card : ℝ) * (K : ℝ)
  let b : ℝ := heathBrownAtkinsonEnergy K * (W.card : ℝ) *
    ((W.card : ℝ) * heathBrownAtkinsonSourceFirstCoefficient T J K)
  let c : ℝ := heathBrownAtkinsonEnergy K * (W.card : ℝ) *
    heathBrownAtkinsonSourceReciprocalContribution T G J K
  have henergy : 0 ≤ heathBrownAtkinsonEnergy K :=
    heathBrownAtkinsonEnergy_nonneg K
  have hfirst : 0 ≤ heathBrownAtkinsonSourceFirstCoefficient T J K :=
    heathBrownAtkinsonSourceFirstCoefficient_nonneg hT
  have hrec : 0 ≤ heathBrownAtkinsonEquation719ReciprocalCoefficient T K :=
    heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg hT
  have hhQ : 0 ≤ harmonic ⌈J / G⌉₊ := by
    rw [harmonic_eq_sum_Icc]
    positivity
  have hh : 0 ≤ (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) := by
    exact_mod_cast hhQ
  have htwoG : 0 ≤ 2 / G := div_nonneg (by norm_num) hG.le
  have hcontrib :
      0 ≤ heathBrownAtkinsonSourceReciprocalContribution T G J K := by
    unfold heathBrownAtkinsonSourceReciprocalContribution
    exact mul_nonneg hrec (mul_nonneg htwoG hh)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg henergy (by positivity)) hcontrib
  have hsq := heathBrownAtkinson_lemma71_source_squared
    hT hG hK hj hblock hSep hRange hDiameter
  have hrow :
      heathBrownAtkinsonEnergy K * (W.card : ℝ) *
          heathBrownAtkinsonSourceRowMajorant T G J K W.card =
        a + b + c := by
    dsimp only [a, b, c]
    unfold heathBrownAtkinsonSourceRowMajorant
      heathBrownAtkinsonSourceReciprocalContribution
    ring
  rw [hrow] at hsq
  have hsqrt :
      (∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖) ≤
        Real.sqrt (a + b + c) := Real.le_sqrt_of_sq_le hsq
  calc
    _ ≤ Real.sqrt (a + b + c) := hsqrt
    _ ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c :=
      sqrt_three_sum_le ha hb hc
    _ = heathBrownAtkinsonLemma71FirstMomentMajorant T G J K W.card := by
      rfl


end

end GafniTao
