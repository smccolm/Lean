import GafniTao.HeathBrownAtkinsonFirstDerivative
import GafniTao.HeathBrownAtkinsonGramBound

/-!
# Kusmin--Landau bound for an Atkinson Gram entry

This file identifies the positively sloped phase from the first-derivative
argument with the literal Gram entry and proves the small-frequency half of
Ivić (7.19).
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- Exact reindexing of the conjugate Gram entry into the positively sloped
phase orientation. -/
theorem heathBrownAtkinsonGram_swap_eq_increasingDifference_range
    (K : ℕ) (t u : ℝ) :
    heathBrownAtkinsonGram K u t =
      ∑ n ∈ Finset.range K,
        RiemannZeta.GuthMaynard.unitaryPhase
          (heathBrownAtkinsonIncreasingDifferenceNat t u (K + 1) n) := by
  rw [heathBrownAtkinsonGram_eq_positiveDifference_range]
  apply Finset.sum_congr rfl
  intro n hn
  unfold heathBrownAtkinsonPositiveDifferenceNat
    heathBrownAtkinsonIncreasingDifferenceNat
  rfl

/-- Literal reciprocal-gap majorant produced by Kusmin--Landau. -/
def heathBrownAtkinsonFirstDerivativeGramMajorant
    (K : ℕ) (t u : ℝ) : ℝ :=
  2 * (2 * K + 1 : ℕ) *
      heathBrownAtkinsonSlopeUpper u (K + 1) / (t - u)

/-- The exact lower derivative scale simplifies to the reciprocal-gap
majorant appearing in the Gram estimate. -/
theorem two_pi_div_firstDerivativeLower_terminal
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) :
    2 * Real.pi /
        heathBrownAtkinsonFirstDerivativeLower u t (K + 1) (2 * K + 1) =
      heathBrownAtkinsonFirstDerivativeGramMajorant K t u := by
  have hgap : t - u ≠ 0 := sub_ne_zero.mpr htu.ne'
  have hB : (2 * K + 1 : ℕ) ≠ 0 := by omega
  have hA : 0 < ((K + 1 : ℕ) : ℝ) := by positivity
  have hs := heathBrownAtkinsonSlopeUpper_pos hu hA
  unfold heathBrownAtkinsonFirstDerivativeLower
    heathBrownAtkinsonFirstDerivativeGramMajorant
  field_simp [hgap, hB, Real.pi_ne_zero, hs.ne']
  push_cast
  ring

/-- Small-frequency Atkinson Gram estimate.  The explicit hypothesis is
exactly the condition ensuring that every unit phase increment lies in the
same half-period; no implicit frequency cutoff is used. -/
theorem norm_heathBrownAtkinsonGram_le_firstDerivativeMajorant_of_small
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u)
    (hsmall :
      heathBrownAtkinsonFirstDerivativeUpper u t (K + 1) (2 * K + 1) ≤
        Real.pi) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonFirstDerivativeGramMajorant K t u := by
  have hKN : K - 1 + 1 = K := by omega
  have hbox : K + 1 + (K - 1) + 2 = 2 * K + 2 := by omega
  have hB : K + 1 + (K - 1) + 1 = 2 * K + 1 := by omega
  have hAreal : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by
    push_cast
    ring
  have hBreal :
      ((K + 1 : ℕ) : ℝ) + ((K - 1 : ℕ) : ℝ) + 1 =
        2 * (K : ℝ) + 1 := by
    exact_mod_cast hB
  have hBreal' :
      (K : ℝ) + 1 + ((K - 1 : ℕ) : ℝ) + 1 =
        2 * (K : ℝ) + 1 := by
    rw [← hAreal]
    exact hBreal
  have hsmall' :
      heathBrownAtkinsonFirstDerivativeUpper u t ((K + 1 : ℕ) : ℝ)
          (((K + 1 : ℕ) : ℝ) + ((K - 1 : ℕ) : ℝ) + 1) ≤ Real.pi := by
    rw [hBreal, hAreal]
    exact hsmall
  have hKL := heathBrownAtkinsonIncreasingDifference_KL
    (K := K + 1) (N := K - 1) hu htu (by omega)
    (by simpa only [hbox] using hblock) htUpper
    hsmall'
  rw [← norm_heathBrownAtkinsonGram_swap K t u,
    heathBrownAtkinsonGram_swap_eq_increasingDifference_range]
  rw [hKN] at hKL
  rw [hBreal, hAreal] at hKL
  exact hKL.trans_eq (two_pi_div_firstDerivativeLower_terminal hu htu)


end

end GafniTao
