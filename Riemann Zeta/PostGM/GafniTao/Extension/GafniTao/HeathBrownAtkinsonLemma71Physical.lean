import GafniTao.HeathBrownAtkinsonSourceHarmonic

/-!
# Physical source majorant for Ivić Lemma 7.1

This is the first complete source-shaped inequality after the harmonic row
has been converted to a logarithm.  The diagonal, exponent-pair, and
reciprocal-spacing contributions are still separate radicals, which lets the
subsequent dyadic Gaussian summation charge each term independently.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators Interval

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The three-radical right side after the literal harmonic ceiling has been
bounded using the physical relation `J / G ≤ T`. -/
def heathBrownAtkinsonLemma71PhysicalMajorant
    (T G J : ℝ) (K R : ℕ) : ℝ :=
  2 *
    (Real.sqrt
        (heathBrownAtkinsonLogEnergy K * (R : ℝ) * (K : ℝ)) +
      Real.sqrt
        (heathBrownAtkinsonLogEnergy K * (R : ℝ) *
          ((R : ℝ) * heathBrownAtkinsonSourceFirstCoefficient T J K)) +
      Real.sqrt
        (heathBrownAtkinsonLogEnergy K * (R : ℝ) *
          (224 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) / G *
            Real.log T)))

/-- The exact averaged-prefix Lemma 7.1 implies the physical three-term
majorant.  This is the source inequality immediately before the monomial
simplification in equation (7.25). -/
theorem heathBrownAtkinson_lemma71_physical
    {K : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 2 ≤ T) (hG : 0 < G) (hJ : 0 ≤ J) (hJG : J / G ≤ T)
    (hK : 1 ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W,
        (‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
          (K : ℝ)⁻¹ *
            (∫ x in (0 : ℝ)..(K : ℝ),
              ‖heathBrownAtkinsonSum x K t‖))) ≤
      heathBrownAtkinsonLemma71PhysicalMajorant T G J K W.card := by
  have hbase := heathBrownAtkinson_lemma71_source_average
    (by linarith : 0 < T) hG hK hblock hSep hRange hDiameter
  have hrec := heathBrownAtkinsonSourceReciprocalContribution_le_log
    hT hG hJ hJG (K := K)
  have henergy : 0 ≤ heathBrownAtkinsonLogEnergy K := by
    unfold heathBrownAtkinsonLogEnergy
    positivity
  have hR : 0 ≤ (W.card : ℝ) := by positivity
  unfold heathBrownAtkinsonLemma71LogMajorant at hbase
  unfold heathBrownAtkinsonLemma71PhysicalMajorant
  calc
    _ ≤ 2 *
        (Real.sqrt
            (heathBrownAtkinsonLogEnergy K * (W.card : ℝ) * (K : ℝ)) +
          Real.sqrt
            (heathBrownAtkinsonLogEnergy K * (W.card : ℝ) *
              ((W.card : ℝ) *
                heathBrownAtkinsonSourceFirstCoefficient T J K)) +
          Real.sqrt
            (heathBrownAtkinsonLogEnergy K * (W.card : ℝ) *
              heathBrownAtkinsonSourceReciprocalContribution T G J K)) :=
      hbase
    _ ≤ 2 *
        (Real.sqrt
            (heathBrownAtkinsonLogEnergy K * (W.card : ℝ) * (K : ℝ)) +
          Real.sqrt
            (heathBrownAtkinsonLogEnergy K * (W.card : ℝ) *
              ((W.card : ℝ) *
                heathBrownAtkinsonSourceFirstCoefficient T J K)) +
          Real.sqrt
            (heathBrownAtkinsonLogEnergy K * (W.card : ℝ) *
              (224 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) / G *
                Real.log T))) := by
      gcongr

/-- The diagonal radical has the source size `K sqrt R` with an explicit
`(1+log(2K))²` budget. -/
theorem heathBrownAtkinson_diagonal_radical_le
    {K R : ℕ} (hK : 1 ≤ K) :
    Real.sqrt
        (heathBrownAtkinsonLogEnergy K * (R : ℝ) * (K : ℝ)) ≤
      2 * (K : ℝ) * Real.sqrt (R : ℝ) *
        (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) := by
  let L : ℝ := 1 + Real.log (2 * K : ℕ)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hK)
  have htwoK : (1 : ℝ) ≤ (2 * K : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * K)
  have hL : 1 ≤ L := by
    dsimp only [L]
    have := Real.log_nonneg htwoK
    linarith
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hright :
      0 ≤ 2 * (K : ℝ) * Real.sqrt (R : ℝ) * L ^ (2 : ℕ) := by
    positivity
  apply (Real.sqrt_le_iff).2
  refine ⟨hright, ?_⟩
  unfold heathBrownAtkinsonLogEnergy
  change
    ((2 * K : ℕ) : ℝ) * L ^ (3 : ℕ) * (R : ℝ) * (K : ℝ) ≤
      (2 * (K : ℝ) * Real.sqrt (R : ℝ) * L ^ (2 : ℕ)) ^ (2 : ℕ)
  have hsqrtR : Real.sqrt (R : ℝ) ^ (2 : ℕ) = (R : ℝ) :=
    Real.sq_sqrt hR
  rw [mul_pow, mul_pow, hsqrtR]
  push_cast
  have hL3 : 0 ≤ L ^ (3 : ℕ) := by positivity
  have hfactor : 2 * L ^ (3 : ℕ) ≤ 4 * L ^ (4 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hL hL3
    nlinarith
  have hscale : 0 ≤ (K : ℝ) ^ (2 : ℕ) * (R : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right hfactor hscale
  nlinarith


end

end GafniTao
