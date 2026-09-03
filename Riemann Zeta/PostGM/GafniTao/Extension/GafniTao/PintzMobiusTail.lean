import GafniTao.PintzWeightShift

/-!
# Quantitative tail in Pintz equation (4.4)

The estimates here retain the genuine Möbius coefficient, the near-one
real part of the zeta zero, and the exact cutoff `exp(lambda + 3)`.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- A Möbius `LSeries` term at a near-one point is bounded by the matching
real p-series term. -/
theorem norm_pintzMobius_coefficient_le
    {rho : ℂ} {eta : ℝ} {n : ℕ}
    (hrho : 1 - eta <= rho.re) (hn : 0 < n) :
    ‖LSeries.term
        (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n‖ <=
      1 / (n : ℝ) ^ (1 - eta) := by
  calc
    ‖LSeries.term
        (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n‖ <=
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) rho n‖ :=
      LSeries.norm_term_le rho (moebius_coeff_norm_le_one n)
    _ <= ‖LSeries.term (fun _ : ℕ => (1 : ℂ))
        ((1 - eta : ℝ) : ℂ) n‖ :=
      LSeries.norm_term_le_of_re_le_re (fun _ : ℕ => (1 : ℂ))
        (by simpa using hrho) n
    _ = 1 / (n : ℝ) ^ (1 - eta) := by
      rw [LSeries.norm_term_eq]
      simp [hn.ne']

/-- Exact conversion of the shifted exponential into the `n^{-lambda}`
factor exposed by the rightward contour displacement. -/
theorem pintz_shifted_exponential_eq_rpow
    {lambda : ℝ} {n : ℕ} (hn : 0 < n) :
    Real.exp (lambda + (lambda - Real.log n) * lambda) =
      Real.exp (lambda + lambda ^ 2) / (n : ℝ) ^ lambda := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnReal]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Right-line bound for an individual integer-indexed Pintz weight. -/
theorem norm_pintzMobiusWeight_le_rpow
    {rho : ℂ} {lambda : ℝ} {n : ℕ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) (hn : 0 < n) :
    ‖pintzMobiusWeight rho lambda n‖ <=
      hughesYoungZetaHalfPlaneMajorant *
        (Real.exp (lambda + lambda ^ 2) / (n : ℝ) ^ lambda) *
          Real.sqrt (Real.pi / (1 / lambda)) := by
  rw [pintzMobiusWeight_eq_sourceWeight hn]
  have hbound := norm_pintzSourceWeight_le_rightLine
    (h := lambda - Real.log n) hrho hlambda
  rw [pintz_shifted_exponential_eq_rpow hn] at hbound
  exact hbound

/-- Pointwise tail majorant for the genuine Möbius-weighted summand. -/
theorem norm_pintzMobius_weightedTerm_le
    {rho : ℂ} {eta lambda : ℝ} {n : ℕ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 3 <= lambda) (hn : 0 < n) :
    ‖LSeries.term
        (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
          pintzMobiusWeight rho lambda n‖ <=
      (1 / (n : ℝ) ^ (1 - eta)) *
        (hughesYoungZetaHalfPlaneMajorant *
          (Real.exp (lambda + lambda ^ 2) / (n : ℝ) ^ lambda) *
            Real.sqrt (Real.pi / (1 / lambda))) := by
  rw [norm_mul]
  exact mul_le_mul
    (norm_pintzMobius_coefficient_le hrhoNear hn)
    (norm_pintzMobiusWeight_le_rpow hrhoHalf hlambda hn)
    (norm_nonneg _) (by positivity)

/-- The same pointwise estimate collected as one p-series with exponent
`lambda + 1 - eta`. -/
theorem norm_pintzMobius_weightedTerm_le_pseries
    {rho : ℂ} {eta lambda : ℝ} {n : ℕ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 3 <= lambda) (hn : 0 < n) :
    ‖LSeries.term
        (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
          pintzMobiusWeight rho lambda n‖ <=
      (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + lambda ^ 2) *
            Real.sqrt (Real.pi / (1 / lambda))) *
        (1 / (n : ℝ) ^ (lambda + 1 - eta)) := by
  have hbase := norm_pintzMobius_weightedTerm_le
    hrhoHalf hrhoNear hlambda hn
  calc
    ‖LSeries.term
        (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
          pintzMobiusWeight rho lambda n‖ <=
        (1 / (n : ℝ) ^ (1 - eta)) *
          (hughesYoungZetaHalfPlaneMajorant *
            (Real.exp (lambda + lambda ^ 2) / (n : ℝ) ^ lambda) *
              Real.sqrt (Real.pi / (1 / lambda))) := hbase
    _ = (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + lambda ^ 2) *
            Real.sqrt (Real.pi / (1 / lambda))) *
        (1 / (n : ℝ) ^ (lambda + 1 - eta)) := by
      rw [show lambda + 1 - eta = (1 - eta) + lambda by ring]
      rw [Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
      field_simp

/-- Pintz's literal finite cutoff `Y₁ = Y e³`, with `Y = exp lambda`. -/
noncomputable def pintzMobiusCutoff (lambda : ℝ) : ℕ :=
  Nat.ceil (Real.exp (lambda + 3))

/-- Integers beyond the literal cutoff are beyond `exp(lambda + 3)` as
real numbers. -/
theorem pintzMobiusCutoff_lt_cast
    {lambda : ℝ} {n : ℕ} (hn : pintzMobiusCutoff lambda < n) :
    Real.exp (lambda + 3) < (n : ℝ) := by
  have hceil : Real.exp (lambda + 3) <=
      (pintzMobiusCutoff lambda : ℝ) := by
    exact Nat.le_ceil _
  have hcast : (pintzMobiusCutoff lambda : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact hceil.trans_lt hcast

/-- A tail p-series term is a fixed exponential factor times a term of the
absolutely convergent `3/2`-series. -/
theorem pintz_tail_pseries_pointwise
    {lambda eta : ℝ} {n : ℕ}
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4)
    (hn : pintzMobiusCutoff lambda < n) :
    1 / (n : ℝ) ^ (lambda + 1 - eta) <=
      Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) *
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ := by
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hbase := pintzMobiusCutoff_lt_cast hn
  have hgap : 0 <= lambda - 1 / 2 - eta := by linarith
  have hpow :
      Real.exp (lambda + 3) ^ (lambda - 1 / 2 - eta) <=
        (n : ℝ) ^ (lambda - 1 / 2 - eta) :=
    Real.rpow_le_rpow (Real.exp_pos _).le hbase.le hgap
  have hleft :
      Real.exp (lambda + 3) ^ (lambda - 1 / 2 - eta) =
        Real.exp ((lambda + 3) * (lambda - 1 / 2 - eta)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hinv :
      1 / (n : ℝ) ^ (lambda - 1 / 2 - eta) <=
        Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) := by
    calc
      1 / (n : ℝ) ^ (lambda - 1 / 2 - eta) <=
          1 / (Real.exp (lambda + 3) ^
            (lambda - 1 / 2 - eta)) :=
        one_div_le_one_div_of_le (by positivity) hpow
      _ = Real.exp (-(lambda + 3) *
          (lambda - 1 / 2 - eta)) := by
        rw [hleft, one_div, ← Real.exp_neg]
        congr 1
        ring
  have hnormTerm :
      ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ =
        1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [LSeries.norm_term_eq]
    simp only [if_neg hnPos.ne', norm_one]
    norm_num
  rw [hnormTerm]
  rw [show lambda + 1 - eta = (3 / 2 : ℝ) +
      (lambda - 1 / 2 - eta) by ring]
  rw [Real.rpow_add hnReal]
  have hthreeHalf : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc
    1 / ((n : ℝ) ^ (3 / 2 : ℝ) *
        (n : ℝ) ^ (lambda - 1 / 2 - eta)) =
        (1 / (n : ℝ) ^ (3 / 2 : ℝ)) *
          (1 / (n : ℝ) ^ (lambda - 1 / 2 - eta)) := by field_simp
    _ <= (1 / (n : ℝ) ^ (3 / 2 : ℝ)) *
        Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) *
        (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by ring

/-- The genuine Möbius-weighted summand in Pintz equation (4.2). -/
noncomputable def pintzMobiusWeightedTerm
    (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  LSeries.term
      (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
    pintzMobiusWeight rho lambda n

/-- The part of the genuine series strictly beyond `Y₁ = Y e³`. -/
noncomputable def pintzMobiusTailTerm
    (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  if pintzMobiusCutoff lambda < n then
    pintzMobiusWeightedTerm rho lambda n
  else 0

/-- Absolute summability of the literal tail, proved from the shifted
weight and the fixed `3/2` majorant. -/
theorem summable_norm_pintzMobiusTailTerm
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    Summable (fun n : ℕ => ‖pintzMobiusTailTerm rho lambda n‖) := by
  let C : ℝ := hughesYoungZetaHalfPlaneMajorant *
      Real.exp (lambda + lambda ^ 2) *
        Real.sqrt (Real.pi / (1 / lambda))
  let D : ℝ := Real.exp
    (-(lambda + 3) * (lambda - 1 / 2 - eta))
  have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hCDnonneg : 0 <= C * D := by
    dsimp [C, D]
    positivity
  refine (summable_hughesYoungZetaHalfPlaneMajorant.mul_left (C * D)).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => ?_)
  by_cases hn : pintzMobiusCutoff lambda < n
  · have hterm := norm_pintzMobius_weightedTerm_le_pseries
      (lambda := lambda) (eta := eta) (n := n)
      hrhoHalf hrhoNear (by linarith) (lt_of_le_of_lt (Nat.zero_le _) hn)
    have hp := pintz_tail_pseries_pointwise hlambda heta hn
    rw [pintzMobiusTailTerm, if_pos hn, pintzMobiusWeightedTerm]
    calc
      ‖LSeries.term
          (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
            pintzMobiusWeight rho lambda n‖ <= C *
          (1 / (n : ℝ) ^ (lambda + 1 - eta)) := by
        simpa [C] using hterm
      _ <= C * (D *
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖) :=
        mul_le_mul_of_nonneg_left hp (by
          dsimp [C]
          positivity)
      _ = C * D *
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ := by ring
  · rw [pintzMobiusTailTerm, if_neg hn, norm_zero]
    exact mul_nonneg hCDnonneg (norm_nonneg _)

/-- Quantitative norm bound for the complete literal tail. -/
theorem norm_tsum_pintzMobiusTailTerm_le
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    ‖∑' n : ℕ, pintzMobiusTailTerm rho lambda n‖ <=
      (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + lambda ^ 2) *
            Real.sqrt (Real.pi / (1 / lambda))) *
        Real.exp (-(lambda + 3) * (lambda - 1 / 2 - eta)) *
          hughesYoungZetaHalfPlaneMajorant := by
  let C : ℝ := hughesYoungZetaHalfPlaneMajorant *
      Real.exp (lambda + lambda ^ 2) *
        Real.sqrt (Real.pi / (1 / lambda))
  let D : ℝ := Real.exp
    (-(lambda + 3) * (lambda - 1 / 2 - eta))
  have htailNorm := summable_norm_pintzMobiusTailTerm
    hrhoHalf hrhoNear hlambda heta
  have hmajor :=
    summable_hughesYoungZetaHalfPlaneMajorant.mul_left (C * D)
  have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hCDnonneg : 0 <= C * D := by
    dsimp [C, D]
    positivity
  have hpoint : ∀ n : ℕ,
      ‖pintzMobiusTailTerm rho lambda n‖ <=
        C * D *
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ := by
    intro n
    by_cases hn : pintzMobiusCutoff lambda < n
    · have hterm := norm_pintzMobius_weightedTerm_le_pseries
        (lambda := lambda) (eta := eta) (n := n)
        hrhoHalf hrhoNear (by linarith) (lt_of_le_of_lt (Nat.zero_le _) hn)
      have hp := pintz_tail_pseries_pointwise hlambda heta hn
      rw [pintzMobiusTailTerm, if_pos hn, pintzMobiusWeightedTerm]
      calc
        ‖LSeries.term
            (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) rho n *
              pintzMobiusWeight rho lambda n‖ <= C *
            (1 / (n : ℝ) ^ (lambda + 1 - eta)) := by
          simpa [C] using hterm
        _ <= C * (D *
            ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖) :=
          mul_le_mul_of_nonneg_left hp (by
            dsimp [C]
            exact mul_nonneg (mul_nonneg hHnonneg (by positivity))
              (Real.sqrt_nonneg _))
        _ = _ := by ring
    · rw [pintzMobiusTailTerm, if_neg hn, norm_zero]
      exact mul_nonneg hCDnonneg (norm_nonneg _)
  calc
    ‖∑' n : ℕ, pintzMobiusTailTerm rho lambda n‖ <=
        ∑' n : ℕ, ‖pintzMobiusTailTerm rho lambda n‖ :=
      norm_tsum_le_tsum_norm htailNorm
    _ <= ∑' n : ℕ, C * D *
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (3 / 2 : ℂ) n‖ :=
      htailNorm.tsum_le_tsum hpoint hmajor
    _ = C * D * hughesYoungZetaHalfPlaneMajorant := by
      rw [tsum_mul_left]
      rfl
    _ = _ := by rfl

/-- The complementary finite head through `Y₁`. -/
noncomputable def pintzMobiusHeadTerm
    (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  if n <= pintzMobiusCutoff lambda then
    pintzMobiusWeightedTerm rho lambda n
  else 0

/-- The finite head is summable for the literal reason that its support is
contained in `range (cutoff + 1)`. -/
theorem summable_pintzMobiusHeadTerm
    (rho : ℂ) (lambda : ℝ) :
    Summable (pintzMobiusHeadTerm rho lambda) := by
  apply summable_of_ne_finset_zero (s := Finset.range
    (pintzMobiusCutoff lambda + 1))
  intro n hn
  rw [Finset.mem_range] at hn
  rw [pintzMobiusHeadTerm, if_neg]
  omega

/-- The full genuine series splits pointwise into the literal finite head
and tail. -/
theorem pintzMobiusWeightedTerm_eq_head_add_tail
    (rho : ℂ) (lambda : ℝ) (n : ℕ) :
    pintzMobiusWeightedTerm rho lambda n =
      pintzMobiusHeadTerm rho lambda n +
        pintzMobiusTailTerm rho lambda n := by
  by_cases hn : n <= pintzMobiusCutoff lambda
  · rw [pintzMobiusHeadTerm, if_pos hn, pintzMobiusTailTerm, if_neg]
    · simp
    · omega
  · rw [pintzMobiusHeadTerm, if_neg hn, pintzMobiusTailTerm, if_pos]
    · simp
    · omega

/-- Absolute summability of the complete genuine weighted series in the
near-one range, now obtained from its finite head and quantitative tail. -/
theorem summable_pintzMobiusWeightedTerm
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    Summable (pintzMobiusWeightedTerm rho lambda) := by
  have hhead := summable_pintzMobiusHeadTerm rho lambda
  have htail : Summable (pintzMobiusTailTerm rho lambda) :=
    summable_norm_iff.mp
      (summable_norm_pintzMobiusTailTerm
        hrhoHalf hrhoNear hlambda heta)
  have hadd := hhead.add htail
  exact hadd.congr (fun n =>
    (pintzMobiusWeightedTerm_eq_head_add_tail rho lambda n).symm)

/-- Exact finite-head plus infinite-tail form of Pintz equations
(4.2)--(4.5). -/
theorem pintz_mobius_equation_4_5_exact
    {rho : ℂ} {eta lambda : ℝ}
    (hrhoHalf : 1 / 2 <= rho.re) (hrhoNear : 1 - eta <= rho.re)
    (hlambda : 8 <= lambda) (heta : eta <= 1 / 4) :
    VerticalIntegral' (pintzMobiusIntegrand rho lambda) 3 =
      (∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
          pintzMobiusWeightedTerm rho lambda n) +
        ∑' n : ℕ, pintzMobiusTailTerm rho lambda n := by
  rw [pintz_mobius_equation_4_2_complete hrhoHalf (by linarith)]
  change (∑' n : ℕ, pintzMobiusWeightedTerm rho lambda n) = _
  have hhead := summable_pintzMobiusHeadTerm rho lambda
  have htail : Summable (pintzMobiusTailTerm rho lambda) :=
    summable_norm_iff.mp
      (summable_norm_pintzMobiusTailTerm
        hrhoHalf hrhoNear hlambda heta)
  calc
    (∑' n : ℕ, pintzMobiusWeightedTerm rho lambda n) =
        ∑' n : ℕ, (pintzMobiusHeadTerm rho lambda n +
          pintzMobiusTailTerm rho lambda n) := by
      apply tsum_congr
      intro n
      exact pintzMobiusWeightedTerm_eq_head_add_tail rho lambda n
    _ = (∑' n : ℕ, pintzMobiusHeadTerm rho lambda n) +
        ∑' n : ℕ, pintzMobiusTailTerm rho lambda n :=
      hhead.tsum_add htail
    _ = (∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
          pintzMobiusWeightedTerm rho lambda n) +
        ∑' n : ℕ, pintzMobiusTailTerm rho lambda n := by
      congr 1
      rw [tsum_eq_sum (s := Finset.range
        (pintzMobiusCutoff lambda + 1))]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_range] at hn
        rw [pintzMobiusHeadTerm, if_pos]
        omega
      · intro n hn
        rw [Finset.mem_range] at hn
        rw [pintzMobiusHeadTerm, if_neg]
        omega

#print axioms norm_pintzMobius_coefficient_le
#print axioms norm_pintzMobiusWeight_le_rpow
#print axioms norm_pintzMobius_weightedTerm_le
#print axioms norm_pintzMobius_weightedTerm_le_pseries
#print axioms pintz_tail_pseries_pointwise
#print axioms summable_norm_pintzMobiusTailTerm
#print axioms norm_tsum_pintzMobiusTailTerm_le
#print axioms pintz_mobius_equation_4_5_exact

end

end GafniTao
