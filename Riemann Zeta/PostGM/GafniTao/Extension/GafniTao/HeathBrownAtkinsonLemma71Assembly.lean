import GafniTao.HeathBrownAtkinsonLemma71Radicals

/-!
# Source-shaped assembly of Ivić Lemma 7.1

This file removes the three abstract radicals from the physical prefix
estimate.  The result still retains the literal equation-(7.19) first
coefficient and the exact `K + 1`; their conversion to fractional powers is
kept as a separate scale lemma.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators Interval

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Exact square-root extraction for the source equation-(7.19)
coefficient.  This exposes the two nested quarter/eighth-root scales without
introducing an asymptotic replacement. -/
theorem sqrt_heathBrownAtkinsonSourceFirstCoefficient
    {T J : ℝ} {K : ℕ} (hT : 0 < T) :
    Real.sqrt (heathBrownAtkinsonSourceFirstCoefficient T J K) =
      30 * Real.sqrt (Real.sqrt J) /
        Real.sqrt (heathBrownAtkinsonQuarterScale (T / 2) K) := by
  have hq : 0 ≤ heathBrownAtkinsonQuarterScale (T / 2) K :=
    (heathBrownAtkinsonQuarterScale_pos (half_pos hT)).le
  unfold heathBrownAtkinsonSourceFirstCoefficient
  rw [Real.sqrt_div (by positivity) _]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 900)]
  norm_num

/-- The complete averaged-prefix estimate after separately bounding the
diagonal, upper-gap, and reciprocal-spacing radicals. -/
theorem heathBrownAtkinson_lemma71_physical_assembled
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
      4 * (K : ℝ) * Real.sqrt (W.card : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) +
        4 * (W.card : ℝ) * Real.sqrt (K : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) *
          Real.sqrt (heathBrownAtkinsonSourceFirstCoefficient T J K) +
        64 * Real.sqrt (K : ℝ) * Real.sqrt (W.card : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) *
          Real.sqrt (Real.sqrt (T * ((K + 1 : ℕ) : ℝ))) *
          Real.sqrt (Real.log T / G) := by
  have hbase := heathBrownAtkinson_lemma71_physical
    hT hG hJ hJG hK hblock hSep hRange hDiameter
  have hdiag := heathBrownAtkinson_diagonal_radical_le
    (R := W.card) hK
  have hfirst := heathBrownAtkinson_exponentPair_radical_le
    (T := T) (J := J) (R := W.card) (by linarith : 0 < T) hK
  have hrec := heathBrownAtkinson_reciprocal_radical_le
    (T := T) (G := G) (K := K) (R := W.card) hT hG hK
  unfold heathBrownAtkinsonLemma71PhysicalMajorant at hbase
  linarith

/-- The same source estimate with the diameter-sensitive coefficient
expanded into its exact nested-root scale.  This is the algebraic form used
before the dyadic `K` and Gaussian-tail summations. -/
theorem heathBrownAtkinson_lemma71_nestedRoot_assembled
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
      4 * (K : ℝ) * Real.sqrt (W.card : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) +
        120 * (W.card : ℝ) * Real.sqrt (K : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) *
          Real.sqrt (Real.sqrt J) /
          Real.sqrt (heathBrownAtkinsonQuarterScale (T / 2) K) +
        64 * Real.sqrt (K : ℝ) * Real.sqrt (W.card : ℝ) *
          (1 + Real.log (2 * K : ℕ)) ^ (2 : ℕ) *
          Real.sqrt (Real.sqrt (T * ((K + 1 : ℕ) : ℝ))) *
          Real.sqrt (Real.log T / G) := by
  have hbase := heathBrownAtkinson_lemma71_physical_assembled
    hT hG hJ hJG hK hblock hSep hRange hDiameter
  rw [sqrt_heathBrownAtkinsonSourceFirstCoefficient
    (T := T) (J := J) (K := K) (by linarith : 0 < T)] at hbase
  convert hbase using 1
  ring


end

end GafniTao
