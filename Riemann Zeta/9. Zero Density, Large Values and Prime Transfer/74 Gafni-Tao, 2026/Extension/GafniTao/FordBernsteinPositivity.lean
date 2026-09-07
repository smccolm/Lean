import GafniTao.FordExplicitData.BernsteinIntervals

/-!
# Positivity transfer for the exact Ford Bernstein certificate

The eight generated certificates cover `[0, 11 / 10]` by intervals of length
`11 / 80`. Their coefficients are exact rationals, and every equality from
the source polynomial to the Bernstein expansion is proved in Lean.
-/

namespace GafniTao

noncomputable section

theorem eval₂_bernsteinPolynomial_nonneg
    {n k : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x
      (bernsteinPolynomial ℚ n k) := by
  simp only [bernsteinPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_natCast, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_one]
  have hxsub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

theorem eval₂_bernsteinExpansion_nonneg
    (c : ℕ → ℚ) (n : ℕ)
    (hc : ∀ k ∈ Finset.range (n + 1), 0 ≤ c k)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x
      (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (c k) * bernsteinPolynomial ℚ n k) := by
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_nonneg
  intro k hk
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  have hcoeffRat : 0 ≤ c k := hc k hk
  have hcoeff : 0 ≤ (c k : ℝ) := by exact_mod_cast hcoeffRat
  exact mul_nonneg hcoeff (eval₂_bernsteinPolynomial_nonneg hx0 hx1)

macro "prove_ford_bernstein_nonneg" hx0:ident hx1:ident
    coeff:ident expansion:ident : tactic =>
  `(tactic|
    (unfold $expansion
     apply eval₂_bernsteinExpansion_nonneg
     · intro k hk
       exact $coeff (Finset.mem_range.mp hk)
     · exact $hx0
     · exact $hx1))

theorem fordGapBernsteinExpansion0_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion0 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff0_nonneg fordGapBernsteinExpansion0

theorem fordGapBernsteinExpansion1_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion1 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff1_nonneg fordGapBernsteinExpansion1

theorem fordGapBernsteinExpansion2_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion2 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff2_nonneg fordGapBernsteinExpansion2

theorem fordGapBernsteinExpansion3_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion3 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff3_nonneg fordGapBernsteinExpansion3

theorem fordGapBernsteinExpansion4_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion4 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff4_nonneg fordGapBernsteinExpansion4

theorem fordGapBernsteinExpansion5_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion5 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff5_nonneg fordGapBernsteinExpansion5

theorem fordGapBernsteinExpansion6_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion6 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff6_nonneg fordGapBernsteinExpansion6

theorem fordGapBernsteinExpansion7_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) x fordGapBernsteinExpansion7 := by
  prove_ford_bernstein_nonneg hx0 hx1 fordGapBernsteinCoeff7_nonneg fordGapBernsteinExpansion7

macro "prove_ford_gap_interval" y:ident
    eqthm:ident nonnegthm:ident source:ident left:num : tactic =>
  `(tactic|
    (let x : ℝ := (80 * $y - 11 * $left) / 11
     have hx0 : 0 ≤ x := by
       dsimp [x]
       linarith
     have hx1 : x ≤ 1 := by
       dsimp [x]
       linarith
     have h := $nonnegthm hx0 hx1
     rw [← $eqthm] at h
     unfold $source at h
     simp only [Polynomial.eval₂_comp, Polynomial.eval₂_add,
       Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X] at h
     convert h using 1 <;> dsimp [x] <;> norm_num <;> ring_nf))

theorem fordNumericalGapExplicit_nonneg_interval0
    {y : ℝ} (hyl : 0 ≤ y) (hyu : y ≤ 11 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine0_eq_bernstein
    fordGapBernsteinExpansion0_nonneg fordGapAffineSource0 0

theorem fordNumericalGapExplicit_nonneg_interval1
    {y : ℝ} (hyl : 11 / 80 ≤ y) (hyu : y ≤ 22 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine1_eq_bernstein
    fordGapBernsteinExpansion1_nonneg fordGapAffineSource1 1

theorem fordNumericalGapExplicit_nonneg_interval2
    {y : ℝ} (hyl : 22 / 80 ≤ y) (hyu : y ≤ 33 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine2_eq_bernstein
    fordGapBernsteinExpansion2_nonneg fordGapAffineSource2 2

theorem fordNumericalGapExplicit_nonneg_interval3
    {y : ℝ} (hyl : 33 / 80 ≤ y) (hyu : y ≤ 44 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine3_eq_bernstein
    fordGapBernsteinExpansion3_nonneg fordGapAffineSource3 3

theorem fordNumericalGapExplicit_nonneg_interval4
    {y : ℝ} (hyl : 44 / 80 ≤ y) (hyu : y ≤ 55 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine4_eq_bernstein
    fordGapBernsteinExpansion4_nonneg fordGapAffineSource4 4

theorem fordNumericalGapExplicit_nonneg_interval5
    {y : ℝ} (hyl : 55 / 80 ≤ y) (hyu : y ≤ 66 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine5_eq_bernstein
    fordGapBernsteinExpansion5_nonneg fordGapAffineSource5 5

theorem fordNumericalGapExplicit_nonneg_interval6
    {y : ℝ} (hyl : 66 / 80 ≤ y) (hyu : y ≤ 77 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine6_eq_bernstein
    fordGapBernsteinExpansion6_nonneg fordGapAffineSource6 6

theorem fordNumericalGapExplicit_nonneg_interval7
    {y : ℝ} (hyl : 77 / 80 ≤ y) (hyu : y ≤ 88 / 80) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  prove_ford_gap_interval y fordGapAffine7_eq_bernstein
    fordGapBernsteinExpansion7_nonneg fordGapAffineSource7 7

theorem fordNumericalGapExplicit_nonneg
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    0 ≤ Polynomial.eval₂ (Rat.castHom ℝ) y fordNumericalGapExplicit := by
  by_cases h0 : y ≤ 11 / 80
  · exact fordNumericalGapExplicit_nonneg_interval0 hy0 h0
  by_cases h1 : y ≤ 22 / 80
  · exact fordNumericalGapExplicit_nonneg_interval1 (by linarith) h1
  by_cases h2 : y ≤ 33 / 80
  · exact fordNumericalGapExplicit_nonneg_interval2 (by linarith) h2
  by_cases h3 : y ≤ 44 / 80
  · exact fordNumericalGapExplicit_nonneg_interval3 (by linarith) h3
  by_cases h4 : y ≤ 55 / 80
  · exact fordNumericalGapExplicit_nonneg_interval4 (by linarith) h4
  by_cases h5 : y ≤ 66 / 80
  · exact fordNumericalGapExplicit_nonneg_interval5 (by linarith) h5
  by_cases h6 : y ≤ 77 / 80
  · exact fordNumericalGapExplicit_nonneg_interval6 (by linarith) h6
  exact fordNumericalGapExplicit_nonneg_interval7 (by linarith) (by norm_num at hy ⊢; exact hy)

end

end GafniTao
