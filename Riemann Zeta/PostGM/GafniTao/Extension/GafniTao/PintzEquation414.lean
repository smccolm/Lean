import GafniTao.PintzEquation412

/-!
# Pintz equations (4.13)--(4.14): off-diagonal absorption

This module isolates the exact algebra used after equation (4.12).  The
hypothesis called `hOffDiagonalHalf` is equation (4.13) after substitution of
the chosen parameters: twice the off-diagonal contribution is at most the
square of the detected lower bound.  The conclusion is the cardinality bound
coming from the remaining diagonal contribution.
-/

namespace GafniTao

noncomputable section

/-- Algebraic core of Pintz's passage from (4.12) and (4.13) to (4.14).
The proof treats `K = 0` separately, so no hidden nonemptiness or division
assumption is present. -/
theorem pintz_equation_4_14_algebra
    {K V H M D : ℝ}
    (hK : 0 <= K) (hH : 0 <= H) (hD : 0 <= D)
    (hEquation412 : (K * V) ^ 2 <= H * (K ^ 2 * M + K * D))
    (hOffDiagonalHalf : 2 * H * K ^ 2 * M <= (K * V) ^ 2) :
    K * V ^ 2 <= 2 * H * D := by
  by_cases hKZero : K = 0
  · subst K
    simp only [zero_mul]
    positivity
  · have hKPos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKZero)
    have hHalf : H * K ^ 2 * M <= (K * V) ^ 2 / 2 := by
      linarith
    have hRemain : (K * V) ^ 2 / 2 <= H * K * D := by
      nlinarith
    have hKNonneg : 0 <= K := hKPos.le
    nlinarith [sq_nonneg (K * V)]

/-- Finite equation (4.14), obtained from the exact detected polynomial and
Gram expansion.  No asymptotic notation has entered at this point. -/
theorem pintz_equation_4_14
    {xi V M D : ℝ} {Y : ℕ} {W : Finset ℝ}
    (hV : 0 < V) (hM : 0 <= M) (hD : 0 <= D)
    (hlarge : ∀ t ∈ W, V <= ‖pintzDetectedPolynomialIcc xi Y t‖)
    (hoff : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintzGramCorrelation xi Y t u‖ <= M)
    (hdiag : ∀ t ∈ W, ‖pintzGramCorrelation xi Y t t‖ <= D)
    (hOffDiagonalHalf :
      2 * (harmonic Y : ℝ) * (W.card : ℝ) ^ 2 * M <=
        ((W.card : ℝ) * V) ^ 2) :
    (W.card : ℝ) * V ^ 2 <= 2 * (harmonic Y : ℝ) * D := by
  have hH : 0 <= (harmonic Y : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have h412 := pintz_equation_4_12_bounded hV.le hM hlarge hoff hdiag
  exact pintz_equation_4_14_algebra (by positivity) hH hD h412
    hOffDiagonalHalf

#print axioms pintz_equation_4_14_algebra
#print axioms pintz_equation_4_14

end

end GafniTao
