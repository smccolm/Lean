import Tao2026.SmoothNumberSaddleHTSmallBetaEdgeAbsorption

/-!
# Finite-prefix promotion for HT Lemma 6

The contour argument gives a uniform eventual estimate in `y`.  This file
supplies an elementary bound for every fixed initial `y`, allowing one larger
coefficient to promote the tail estimate to the literal all-`y` contract.
-/

open Filter Topology Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace Tao2026

noncomputable section

/-- The finite Mangoldt transform is bounded by Chebyshev's function when
`0 < beta < 1`; the oscillatory factors have norm one and every remaining
real power is at most one. -/
theorem norm_smoothSaddleHTMangoldtTransform_le_psi
    {y : ℕ} {beta t : ℝ} (hbetaOne : beta < 1) :
    ‖smoothSaddleHTMangoldtTransform y beta t‖ ≤ Chebyshev.psi y := by
  unfold smoothSaddleHTMangoldtTransform
  calc
    ‖∑ n ∈ Finset.Icc 1 y,
        (((Λ n : ℝ) * (n : ℝ) ^ (beta - 1) : ℝ) : ℂ) *
          Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑ n ∈ Finset.Icc 1 y,
        ‖((((Λ n : ℝ) * (n : ℝ) ^ (beta - 1) : ℝ) : ℂ) *
          Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 y, (Λ n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnOneNat : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnOneNat
      have hpow : (n : ℝ) ^ (beta - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
      have hLambda : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hexp :
          ‖Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        convert Complex.norm_exp_ofReal_mul_I (-(t * Real.log n)) using 1
        push_cast
        ring
      rw [norm_mul, hexp, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hLambda (Real.rpow_nonneg (by positivity) _))]
      exact mul_le_of_le_one_right hLambda hpow
    _ = Chebyshev.psi y := by
      rw [Chebyshev.psi_eq_sum_Icc]
      norm_num
      have hsets : Finset.Icc 0 y = insert 0 (Finset.Icc 1 y) := by
        ext n
        simp
        omega
      rw [hsets]
      simp

/-- For positive `beta < 1`, the HT main term is bounded by the elementary
quantity `y / beta`. -/
theorem norm_smoothSaddleHTMangoldtMainTerm_le_div
    {y : ℕ} {beta t : ℝ} (hy : 1 ≤ y) (hbeta : 0 < beta)
    (hbetaOne : beta < 1) :
    ‖smoothSaddleHTMangoldtMainTerm y beta t‖ ≤ (y : ℝ) / beta := by
  rw [norm_smoothSaddleHTMangoldtMainTerm]
  have hyOne : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hpowNonneg : 0 ≤ (y : ℝ) ^ beta := Real.rpow_nonneg (by positivity) _
  have hpow : (y : ℝ) ^ beta ≤ (y : ℝ) := by
    convert Real.rpow_le_rpow_of_exponent_le hyOne (le_of_lt hbetaOne) using 1
    rw [Real.rpow_one]
  have hsqrt : beta ≤ Real.sqrt (beta ^ 2 + t ^ 2) := by
    apply (Real.le_sqrt hbeta.le (by positivity)).2
    nlinarith [sq_nonneg t]
  rw [abs_of_nonneg hpowNonneg]
  calc
    (y : ℝ) ^ beta / Real.sqrt (beta ^ 2 + t ^ 2) ≤
        (y : ℝ) / Real.sqrt (beta ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_right hpow (Real.sqrt_nonneg _)
    _ ≤ (y : ℝ) / beta :=
      div_le_div_of_nonneg_left (by positivity) hbeta hsqrt

/-- The literal HT error majorant dominates `1 / beta`. -/
theorem one_div_le_smoothSaddleHTMangoldtError
    (y : ℕ) {beta epsilon : ℝ} (hbeta : 0 < beta) :
    1 / beta ≤ smoothSaddleHTMangoldtError y beta epsilon := by
  unfold smoothSaddleHTMangoldtError
  have hinv : 0 ≤ 1 / beta := by positivity
  have htail : 0 ≤ (y : ℝ) ^ beta *
      Real.exp (-(Real.log y) ^ (epsilon / 2)) := by positivity
  calc
    1 / beta = (1 / beta) * 1 := by ring
    _ ≤ (1 / beta) *
        (1 + (y : ℝ) ^ beta *
          Real.exp (-(Real.log y) ^ (epsilon / 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) hinv

/-- A uniform elementary estimate, deliberately coarse but valid for every
`y ≥ 2`.  Its coefficient depends only on `y`, so a bounded initial segment
can be absorbed into a single enlarged HT constant. -/
theorem norm_smoothSaddleHTMangoldtTransform_sub_mainTerm_le_crude
    {y : ℕ} {beta epsilon t : ℝ} (hy : 2 ≤ y)
    (hbeta : 0 < beta) (hbetaOne : beta < 1) :
    ‖smoothSaddleHTMangoldtTransform y beta t -
        smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
      (Chebyshev.psi y + (y : ℝ)) *
        smoothSaddleHTMangoldtError y beta epsilon := by
  have htransform :=
    norm_smoothSaddleHTMangoldtTransform_le_psi (y := y) (t := t) hbetaOne
  have hmain := norm_smoothSaddleHTMangoldtMainTerm_le_div
    (y := y) (t := t) (by omega) hbeta hbetaOne
  have herrorInv := one_div_le_smoothSaddleHTMangoldtError
    (epsilon := epsilon) y hbeta
  have hinvOne : 1 ≤ 1 / beta := by
    rw [le_div_iff₀ hbeta]
    linarith
  have herrorOne : 1 ≤ smoothSaddleHTMangoldtError y beta epsilon :=
    hinvOne.trans herrorInv
  have hpsi : 0 ≤ Chebyshev.psi (y : ℝ) := Chebyshev.psi_nonneg _
  have hyNonneg : 0 ≤ (y : ℝ) := by positivity
  calc
    ‖smoothSaddleHTMangoldtTransform y beta t -
        smoothSaddleHTMangoldtMainTerm y beta t‖ ≤
        ‖smoothSaddleHTMangoldtTransform y beta t‖ +
          ‖smoothSaddleHTMangoldtMainTerm y beta t‖ := norm_sub_le _ _
    _ ≤ Chebyshev.psi y + (y : ℝ) / beta := add_le_add htransform hmain
    _ ≤ Chebyshev.psi y * smoothSaddleHTMangoldtError y beta epsilon +
        (y : ℝ) * smoothSaddleHTMangoldtError y beta epsilon := by
      gcongr
      · simpa using mul_le_mul_of_nonneg_left herrorOne hpsi
      · simpa [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left herrorInv hyNonneg
    _ = (Chebyshev.psi y + (y : ℝ)) *
        smoothSaddleHTMangoldtError y beta epsilon := by ring

/-- The eventual contour estimate can be enlarged once to cover the finite
initial segment, producing the exact fixed-`epsilon` HT contract. -/
theorem exists_smoothSaddleHTMangoldtTransformEstimateAt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1) :
    ∃ C : ℝ, SmoothSaddleHTMangoldtTransformEstimateAt epsilon C := by
  obtain ⟨C₀, hC₀, hEventually⟩ :=
    exists_smoothSaddleHT_eventually_transform_le_error hepsilon hepsilonOne
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.1 hEventually
  let C : ℝ := max C₀ (Chebyshev.psi Y + (Y : ℝ))
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y beta t hy hbeta hbetaOne ht
  have herror : 0 ≤ smoothSaddleHTMangoldtError y beta epsilon :=
    smoothSaddleHTMangoldtError_nonneg y hbeta
  by_cases hTail : Y ≤ y
  · exact (hY y hTail beta t hbeta hbetaOne ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) herror)
  · have hyY : y ≤ Y := Nat.le_of_lt (lt_of_not_ge hTail)
    have hyYReal : (y : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hyY
    have hcoefficient : Chebyshev.psi y + (y : ℝ) ≤
        Chebyshev.psi Y + (Y : ℝ) :=
      add_le_add (Chebyshev.psi_mono hyYReal) hyYReal
    exact (norm_smoothSaddleHTMangoldtTransform_sub_mainTerm_le_crude
      hy hbeta hbetaOne).trans
        (mul_le_mul_of_nonneg_right
          (hcoefficient.trans (le_max_right _ _)) herror)

/-- HT Lemma 6, with the source's uniformity in `y`, `beta`, and frequency
and with an `epsilon`-dependent implied constant. -/
theorem smoothSaddleHTMangoldtTransformEstimate :
    SmoothSaddleHTMangoldtTransformEstimate := by
  intro epsilon hepsilon hepsilonOne
  exact exists_smoothSaddleHTMangoldtTransformEstimateAt
    hepsilon hepsilonOne

end

end Tao2026
