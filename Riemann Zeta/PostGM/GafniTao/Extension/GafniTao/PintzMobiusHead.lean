import GafniTao.PintzMobiusTail

/-!
# Pintz's truncated Möbius sum

This file combines the exact finite-head decomposition with the complete
Gaussian identity.  The error term is deliberately kept in its proved
explicit form; no use is made of the informal `O(Y⁻²)` abbreviation in the
source.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal finite sum through Pintz's cutoff `Y₁ = exp (λ + 3)`. -/
noncomputable def pintzMobiusFiniteHead (rho : ℂ) (lambda : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
    pintzMobiusWeightedTerm rho lambda n

/-- The explicit absolute tail majorant proved from the genuine Möbius
series and Pintz's Gaussian weight. -/
noncomputable def pintzMobiusTailBound (eta lambda : ℝ) : ℝ :=
  (hughesYoungZetaHalfPlaneMajorant *
      Real.exp (lambda + lambda ^ 2) *
        Real.sqrt (Real.pi / (1 / lambda))) *
    Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) *
      hughesYoungZetaHalfPlaneMajorant

/-- The complete Möbius series is exactly the finite head plus the literal
tail. -/
theorem pintzMobius_complete_eq_finiteHead_add_tail
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    (∑' n : ℕ, pintzMobiusWeightedTerm rho lambda n) =
      pintzMobiusFiniteHead rho lambda +
        ∑' n : ℕ, pintzMobiusTailTerm rho lambda n := by
  change (∑' n : ℕ,
      LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
        pintzMobiusWeight rho lambda n) = _
  rw [← pintz_mobius_equation_4_2_complete hrhoHalf (by linarith)]
  simpa [pintzMobiusFiniteHead] using
    (pintz_mobius_equation_4_5_exact
      hrhoHalf hrhoNear hlambda heta)

/-- Quantitative finite form of Pintz equation (4.5).  This is the precise
error ledger used below: the bare Gaussian contributes `exp (-2λ)` and the
discarded Möbius tail contributes `pintzMobiusTailBound η λ`. -/
theorem norm_pintzMobiusFiniteHead_sub_one_le
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    ‖pintzMobiusFiniteHead rho lambda - 1‖ <=
      Real.exp (-2 * lambda) + pintzMobiusTailBound eta lambda := by
  have hsplit := pintzMobius_complete_eq_finiteHead_add_tail
    hrhoHalf hrhoNear hlambda heta
  have hcomplete := pintz_mobius_complete_series_ne_one
    hrhoHalf hlambda
  have htail := norm_tsum_pintzMobiusTailTerm_le
    hrhoHalf hrhoNear hlambda heta
  change ‖pintzMobiusFiniteHead rho lambda - 1‖ <= _
  calc
    ‖pintzMobiusFiniteHead rho lambda - 1‖ =
        ‖((∑' n : ℕ, pintzMobiusWeightedTerm rho lambda n) - 1) -
          ∑' n : ℕ, pintzMobiusTailTerm rho lambda n‖ := by
      rw [hsplit]
      ring_nf
    _ <= ‖(∑' n : ℕ, pintzMobiusWeightedTerm rho lambda n) - 1‖ +
        ‖∑' n : ℕ, pintzMobiusTailTerm rho lambda n‖ := norm_sub_le _ _
    _ <= Real.exp (-2 * lambda) + pintzMobiusTailBound eta lambda := by
      exact add_le_add hcomplete (by simpa [pintzMobiusTailBound] using htail)

/-- A simpler exponential envelope for the literal Möbius tail.  The
exponent `-3λ/4 + 9/4` records the loss from the Gaussian integral and the
full allowed near-one range `η ≤ 1/4`. -/
theorem pintzMobiusTailBound_le_explicit
    {eta lambda : ℝ} (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    pintzMobiusTailBound eta lambda <=
      hughesYoungZetaHalfPlaneMajorant ^ 2 *
        Real.exp (-(3 / 4 : ℝ) * lambda + 9 / 4) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hpiLambda : Real.pi * lambda <= lambda ^ 2 := by
    have hpi : Real.pi <= lambda := by nlinarith [Real.pi_lt_four]
    nlinarith
  have hsqrt : Real.sqrt (Real.pi / (1 / lambda)) <= lambda := by
    rw [show Real.pi / (1 / lambda) = Real.pi * lambda by field_simp]
    rw [Real.sqrt_le_iff]
    exact ⟨hlambdaPos.le, hpiLambda⟩
  have hlambdaExp : lambda <= Real.exp (lambda / 2) := by
    have hpow := Real.quadratic_le_exp_of_nonneg
      (by positivity : 0 <= lambda / 2)
    nlinarith [sq_nonneg (lambda - 8)]
  have hsqrtExp : Real.sqrt (Real.pi / (1 / lambda)) <=
      Real.exp (lambda / 2) := hsqrt.trans hlambdaExp
  have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hetaLambda : eta * lambda <= (1 / 4 : ℝ) * lambda :=
    mul_le_mul_of_nonneg_right heta hlambdaPos.le
  have hexp :
      Real.exp (lambda + lambda ^ 2) * Real.exp (lambda / 2) *
          Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) =
        Real.exp ((lambda + lambda ^ 2) + lambda / 2 +
          (-(lambda + 3) * (lambda - 1 / 2 - eta))) := by
    rw [← Real.exp_add, ← Real.exp_add]
  unfold pintzMobiusTailBound
  calc
    (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + lambda ^ 2) *
            Real.sqrt (Real.pi / (1 / lambda))) *
        Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) *
          hughesYoungZetaHalfPlaneMajorant
        <= (hughesYoungZetaHalfPlaneMajorant *
              Real.exp (lambda + lambda ^ 2) *
                Real.exp (lambda / 2)) *
            Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) *
              hughesYoungZetaHalfPlaneMajorant := by
          gcongr
    _ = hughesYoungZetaHalfPlaneMajorant ^ 2 *
        Real.exp ((lambda + lambda ^ 2) + lambda / 2 +
          (-(lambda + 3) * (lambda - 1 / 2 - eta))) := by
      rw [← hexp]
      ring
    _ <= hughesYoungZetaHalfPlaneMajorant ^ 2 *
        Real.exp (-(3 / 4 : ℝ) * lambda + 9 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Once the fixed half-plane constant is absorbed, the genuine discarded
tail is at most `exp (-λ/2)`. -/
theorem pintzMobiusTailBound_le_exp_neg_half
    {eta lambda : ℝ} (hlambda : 8 <= lambda) (heta : eta <= 1 / 4)
    (habsorb : hughesYoungZetaHalfPlaneMajorant ^ 2 <=
      Real.exp (lambda / 4 - 9 / 4)) :
    pintzMobiusTailBound eta lambda <= Real.exp (-lambda / 2) := by
  calc
    pintzMobiusTailBound eta lambda <=
        hughesYoungZetaHalfPlaneMajorant ^ 2 *
          Real.exp (-(3 / 4 : ℝ) * lambda + 9 / 4) :=
      pintzMobiusTailBound_le_explicit hlambda heta
    _ <= Real.exp (lambda / 4 - 9 / 4) *
        Real.exp (-(3 / 4 : ℝ) * lambda + 9 / 4) :=
      mul_le_mul_of_nonneg_right habsorb (Real.exp_nonneg _)
    _ = Real.exp (-lambda / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The explicit real threshold which absorbs the sole fixed Dirichlet-series
constant in Pintz's finite Möbius detector. -/
noncomputable def pintzMobiusLambdaThreshold : ℝ :=
  max 8 (4 *
    (Real.log (max 1 (hughesYoungZetaHalfPlaneMajorant ^ 2)) + 9 / 4))

theorem pintzMobiusLambdaThreshold_ge_eight :
    8 <= pintzMobiusLambdaThreshold :=
  le_max_left _ _

/-- The threshold really absorbs the fixed half-plane majorant. -/
theorem pintzMobius_majorant_absorbed
    {lambda : ℝ} (hlambda : pintzMobiusLambdaThreshold <= lambda) :
    hughesYoungZetaHalfPlaneMajorant ^ 2 <=
      Real.exp (lambda / 4 - 9 / 4) := by
  let Q : ℝ := max 1 (hughesYoungZetaHalfPlaneMajorant ^ 2)
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hthreshold :
      4 * (Real.log Q + 9 / 4) <= lambda := by
    exact (le_max_right 8
      (4 * (Real.log Q + 9 / 4))).trans hlambda
  have hlog : Real.log Q <= lambda / 4 - 9 / 4 := by
    linarith
  calc
    hughesYoungZetaHalfPlaneMajorant ^ 2 <= Q := le_max_right _ _
    _ = Real.exp (Real.log Q) := (Real.exp_log hQpos).symm
    _ <= Real.exp (lambda / 4 - 9 / 4) := Real.exp_le_exp.mpr hlog

/-- At the explicit threshold, the sum of the Gaussian and Möbius-tail
errors is at most one half. -/
theorem pintzMobius_total_error_le_one_half
    {eta lambda : ℝ} (hlambda : pintzMobiusLambdaThreshold <= lambda)
    (heta : eta <= 1 / 4) :
    Real.exp (-2 * lambda) + pintzMobiusTailBound eta lambda <= 1 / 2 := by
  have hlambdaEight : 8 <= lambda :=
    pintzMobiusLambdaThreshold_ge_eight.trans hlambda
  have htail : pintzMobiusTailBound eta lambda <= Real.exp (-lambda / 2) :=
    pintzMobiusTailBound_le_exp_neg_half hlambdaEight heta
      (pintzMobius_majorant_absorbed hlambda)
  have hexpFour : Real.exp (-4) <= (1 / 4 : ℝ) := by
    rw [Real.exp_neg]
    have h : 1 / Real.exp 4 <= (1 / 4 : ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos 4)]
      nlinarith [Real.add_one_le_exp 4]
    simpa only [one_div] using h
  have hfirst : Real.exp (-2 * lambda) <= Real.exp (-4) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hsecond : Real.exp (-lambda / 2) <= Real.exp (-4) := by
    apply Real.exp_le_exp.mpr
    linarith
  linarith

/-- Whenever the explicit two-part error is below one half, the finite
Möbius sum has the lower bound used in Pintz's zero detector. -/
theorem one_half_le_norm_pintzMobiusFiniteHead
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4)
    (herror : Real.exp (-2 * lambda) +
      pintzMobiusTailBound eta lambda <= 1 / 2) :
    1 / 2 <= ‖pintzMobiusFiniteHead rho lambda‖ := by
  have hnear := norm_pintzMobiusFiniteHead_sub_one_le
    hrhoHalf hrhoNear hlambda heta
  have hreverse : ‖(1 : ℂ)‖ - ‖pintzMobiusFiniteHead rho lambda‖ <=
      ‖(1 : ℂ) - pintzMobiusFiniteHead rho lambda‖ :=
    norm_sub_norm_le (1 : ℂ) (pintzMobiusFiniteHead rho lambda)
  rw [norm_one, norm_sub_rev] at hreverse
  linarith

/-- Fully discharged finite Möbius detector in Pintz's near-one range. -/
theorem one_half_le_norm_pintzMobiusFiniteHead_of_large
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : pintzMobiusLambdaThreshold <= lambda)
    (heta : eta <= 1 / 4) :
    1 / 2 <= ‖pintzMobiusFiniteHead rho lambda‖ := by
  exact one_half_le_norm_pintzMobiusFiniteHead
    hrhoHalf hrhoNear
    (pintzMobiusLambdaThreshold_ge_eight.trans hlambda) heta
    (pintzMobius_total_error_le_one_half hlambda heta)

#print axioms pintzMobius_complete_eq_finiteHead_add_tail
#print axioms norm_pintzMobiusFiniteHead_sub_one_le
#print axioms one_half_le_norm_pintzMobiusFiniteHead
#print axioms pintzMobiusTailBound_le_explicit
#print axioms pintzMobius_total_error_le_one_half
#print axioms one_half_le_norm_pintzMobiusFiniteHead_of_large

end

end GafniTao
