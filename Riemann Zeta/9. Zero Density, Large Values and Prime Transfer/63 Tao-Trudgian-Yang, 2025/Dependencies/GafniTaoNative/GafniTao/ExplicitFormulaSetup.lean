import GafniTao.ZeroEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The zero terms in Gafni--Tao equations (2.3)--(2.4)

This module fixes the sign, multiplicity, interval, and coefficient
conventions before the truncated explicit formula is proved.  It does not
claim the explicit formula itself.
-/

open Complex Finset Set
open scoped BigOperators Interval

namespace GafniTao

/-- The coefficient `c_rho` after factoring `x^rho` from the short increment.
The parameter `tau` is kept literal. -/
noncomputable def zeroIncrementCoefficient (tau : ℝ) (rho : ℂ) : ℂ :=
  (((1 + 1 / tau : ℝ) : ℂ) ^ rho - 1) / rho

/-- The literal summand in equation (2.4), before its global sign is chosen by
the explicit formula. -/
noncomputable def zeroIncrementTerm (tau x : ℝ) (rho : ℂ) : ℂ :=
  (((x + x / tau : ℝ) : ℂ) ^ rho - (x : ℂ) ^ rho) / rho

/-- The multiplicity-weighted zero sum over a closed real-part strip and the
frozen symmetric ordinate rectangle. -/
noncomputable def zeroStripIncrementSum
    (sigmaLower sigmaUpper T tau x : ℝ) : ℂ :=
  ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      sigmaLower sigmaUpper (-T) T,
    (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho

/-- The source coefficient is an exact integral of `u^(rho-1)`. -/
theorem zeroIncrementCoefficient_eq_integral
    {tau : ℝ} (htau : 0 < tau) {rho : ℂ} (hrho : rho ≠ 0) :
    zeroIncrementCoefficient tau rho =
      ∫ u : ℝ in 1..1 + 1 / tau, (u : ℂ) ^ (rho - 1) := by
  have hinv : 0 ≤ 1 / tau := one_div_nonneg.mpr htau.le
  have hupper : 1 ≤ 1 + 1 / tau := by linarith
  have hzero : (0 : ℝ) ∉ [[(1 : ℝ), 1 + 1 / tau]] := by
    rw [uIcc_of_le hupper]
    simp
  have hexponent : rho - 1 ≠ (-1 : ℂ) := by
    intro h
    apply hrho
    linear_combination h
  rw [integral_cpow (Or.inr ⟨hexponent, hzero⟩)]
  simp [zeroIncrementCoefficient]

/-- Uniform source bound for `c_rho` on the closed critical strip.  This is
the literal `|c_rho| <= 1/tau` estimate used after equation (2.4), proved
from the integral representation rather than division by a possibly small
ordinate. -/
theorem norm_zeroIncrementCoefficient_le
    {tau : ℝ} (htau : 0 < tau) {rho : ℂ} (hrho : rho ≠ 0)
    (hrhoRe : rho.re ≤ 1) :
    ‖zeroIncrementCoefficient tau rho‖ ≤ 1 / tau := by
  rw [zeroIncrementCoefficient_eq_integral htau hrho]
  calc
    ‖∫ u : ℝ in 1..1 + 1 / tau, (u : ℂ) ^ (rho - 1)‖
        ≤ 1 * |(1 + 1 / tau) - 1| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro u hu
          have hinv : 0 ≤ 1 / tau := one_div_nonneg.mpr htau.le
          have hupper : 1 ≤ 1 + 1 / tau := by linarith
          rw [uIoc_of_le hupper] at hu
          have huPos : 0 < u := zero_lt_one.trans hu.1
          rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos]
          exact Real.rpow_le_one_of_one_le_of_nonpos hu.1.le
            (by simpa using sub_nonpos.mpr hrhoRe)
    _ = 1 / tau := by
      have hinv : 0 ≤ 1 / tau := one_div_nonneg.mpr htau.le
      rw [abs_of_nonneg]
      · ring
      · linarith

/-- A zero in a rectangle whose lower real edge is positive cannot be the
complex number zero.  This discharges the denominator condition from the
actual zero-set membership rather than leaving it as a consumer hypothesis. -/
theorem ne_zero_of_mem_zerosInRect_of_pos
    {sigmaLower sigmaUpper TLower TUpper : ℝ}
    (hsigmaLower : 0 < sigmaLower) {rho : ℂ}
    (hrho : rho ∈ RiemannZeta.GuthMaynard.zerosInRect
      sigmaLower sigmaUpper TLower TUpper) :
    rho ≠ 0 := by
  rw [RiemannZeta.GuthMaynard.zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, RiemannZeta.GuthMaynard.mem_ZeroRectangle] at hrho
  intro hrhoZero
  subst rho
  simpa using (not_le_of_gt hsigmaLower hrho.1.1)

/-- Factoring out the physical scale gives exactly the coefficient used in
the paper's second- and fourth-moment expansions. -/
theorem zeroIncrementTerm_eq_cpow_mul_coefficient
    {tau x : ℝ} (htau : 0 < tau) (hx : 0 ≤ x) (rho : ℂ) :
    zeroIncrementTerm tau x rho =
      (x : ℂ) ^ rho * zeroIncrementCoefficient tau rho := by
  have hfactor : 0 ≤ 1 + 1 / tau := by positivity
  have hbase : x + x / tau = x * (1 + 1 / tau) := by ring
  rw [zeroIncrementTerm, zeroIncrementCoefficient, hbase]
  rw [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hx hfactor]
  ring

/-- Pointwise size of the literal zero increment on the closed critical
strip.  This is the termwise estimate that feeds the paper's strip moments. -/
theorem norm_zeroIncrementTerm_le
    {tau x : ℝ} (htau : 0 < tau) (hx : 0 < x) {rho : ℂ}
    (hrho : rho ≠ 0) (hrhoRe : rho.re ≤ 1) :
    ‖zeroIncrementTerm tau x rho‖ ≤ x ^ rho.re / tau := by
  rw [zeroIncrementTerm_eq_cpow_mul_coefficient htau hx.le, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hc := norm_zeroIncrementCoefficient_le htau hrho hrhoRe
  exact (mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hx.le rho.re)).trans_eq
    (by ring)

/-- Unfolding the public strip sum exposes the product analytic multiplicity
and the literal equation-(2.4) summand. -/
theorem zeroStripIncrementSum_eq_weighted_sum
    (sigmaLower sigmaUpper T tau x : ℝ) :
    zeroStripIncrementSum sigmaLower sigmaUpper T tau x =
      ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
          sigmaLower sigmaUpper (-T) T,
        (RiemannZeta.GuthMaynard.analyticVanishingOrder
            riemannZeta rho : ℂ) *
          ((((x + x / tau : ℝ) : ℂ) ^ rho - (x : ℂ) ^ rho) / rho) := by
  rfl

end GafniTao
