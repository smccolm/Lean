import GafniTao.HeathBrownAtkinsonLemma71Average
import GafniTao.HeathBrownAtkinsonPhysicalCoefficients

/-!
# Physical coefficients in Ivić's source form of Lemma 7.1

Ivić equation (7.25) uses the diameter `J`, rather than the ambient height,
in the B-process contribution.  This file removes the remaining nested
quarter-power from that exact source coefficient.  The resulting identity is
the algebraic origin of the factor

`J^(1/4) * T^(-1/8) * K^(5/8)`

after the coefficient is placed under the square root in Lemma 7.1.  No
asymptotic comparison or replacement of `K+1` by `K` is made here.
-/

namespace GafniTao

noncomputable section

open Set
open RiemannZeta.GuthMaynard

/-- The fourth power of the literal diameter-sensitive coefficient is
`900^4 J^2 2(K+1)/T`.  This is the exact scale identity behind the
exponent-pair term in Ivić equation (7.25). -/
theorem heathBrownAtkinsonSourceFirstCoefficient_pow_four
    {T J : ℝ} {K : ℕ} (hT : 0 < T) (hJ : 0 ≤ J) :
    heathBrownAtkinsonSourceFirstCoefficient T J K ^ (4 : ℕ) =
      900 ^ (4 : ℕ) * J ^ (2 : ℕ) *
        (2 * ((K + 1 : ℕ) : ℝ)) / T := by
  have hq : 0 < heathBrownAtkinsonQuarterScale (T / 2) K :=
    heathBrownAtkinsonQuarterScale_pos (half_pos hT)
  have hq4 := heathBrownAtkinsonQuarterScale_pow_four
    (K := K) (show 0 ≤ T / 2 by positivity)
  have hsqrt4 : Real.sqrt J ^ (4 : ℕ) = J ^ (2 : ℕ) := by
    calc
      Real.sqrt J ^ (4 : ℕ) =
          (Real.sqrt J ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = J ^ (2 : ℕ) := by rw [Real.sq_sqrt hJ]
  unfold heathBrownAtkinsonSourceFirstCoefficient
  rw [div_pow, mul_pow, hsqrt4, hq4]
  field_simp [hT.ne', hq.ne']

/-- The reciprocal part of the source row is exactly the equation-(7.19)
coefficient times the scaled harmonic spacing sum.  The lemma is retained as
an equality so later power estimates cannot silently lose the factor `2/G`
or replace `ceil(J/G)` by an unrelated cutoff. -/
theorem heathBrownAtkinsonSourceReciprocalContribution_eq
    (T G J : ℝ) (K : ℕ) :
    heathBrownAtkinsonSourceReciprocalContribution T G J K =
      28 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) *
        ((2 / G) * (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ))) := by
  rfl

/-- The complete averaged-prefix estimate with the source coefficients
unfolded.  This is the exact finite inequality inserted into Ivić Theorem
6.2 before dyadic `K` selection; all three radicals and the factor two remain
visible. -/
theorem heathBrownAtkinson_lemma71_source_average_unfolded
    {K : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 1 ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W,
        (‖heathBrownAtkinsonSum (K : ℝ) K t‖ +
          (K : ℝ)⁻¹ *
            (∫ x in (0 : ℝ)..(K : ℝ),
              ‖heathBrownAtkinsonSum x K t‖))) ≤
      2 *
        (Real.sqrt
            ((((2 * K : ℕ) : ℝ) *
                (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ)) *
              (W.card : ℝ) * (K : ℝ)) +
          Real.sqrt
            ((((2 * K : ℕ) : ℝ) *
                (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ)) *
              (W.card : ℝ) *
                ((W.card : ℝ) *
                  (900 * Real.sqrt J /
                    heathBrownAtkinsonQuarterScale (T / 2) K))) +
          Real.sqrt
            ((((2 * K : ℕ) : ℝ) *
                (1 + Real.log (2 * K : ℕ)) ^ (3 : ℕ)) *
              (W.card : ℝ) *
                (28 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) *
                  ((2 / G) *
                    (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)))))) := by
  simpa only [heathBrownAtkinsonLemma71LogMajorant,
    heathBrownAtkinsonLogEnergy,
    heathBrownAtkinsonSourceFirstCoefficient,
    heathBrownAtkinsonSourceReciprocalContribution,
    heathBrownAtkinsonEquation719ReciprocalCoefficient] using
      heathBrownAtkinson_lemma71_source_average
        hT hG hK hblock hSep hRange hDiameter


end

end GafniTao
