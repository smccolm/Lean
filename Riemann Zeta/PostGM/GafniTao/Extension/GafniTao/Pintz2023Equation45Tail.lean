import GafniTao.Pintz2023GaussianWeightShift
import GafniTao.PintzMobiusTail

/-!
# Pintz (2023), equations (4.3)--(4.6): the finite-mollifier tail

The coefficient here is the source coefficient
`a_n = ∑_{d ∣ n, d ≤ X} μ(d)`, not the Möbius coefficient from the older
auxiliary contour experiment.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintz2023Cutoff_eq_pintzMobiusCutoff (lambda : ℝ) :
    pintz2023Cutoff lambda = pintzMobiusCutoff lambda := rfl

theorem pintz2023Cutoff_lt_cast
    {lambda : ℝ} {n : ℕ} (hn : pintz2023Cutoff lambda < n) :
    Real.exp (lambda + 3) < (n : ℝ) := by
  rw [pintz2023Cutoff_eq_pintzMobiusCutoff] at hn
  exact pintzMobiusCutoff_lt_cast hn

/-- The actual finite-mollifier Dirichlet coefficient at a near-one point,
before applying the divisor bound. -/
theorem norm_pintz2023_LSeries_term_le
    {X n : ℕ} {rho : ℂ} {eta : ℝ}
    (hrho : 1 - eta ≤ rho.re) (hn : 0 < n) :
    ‖LSeries.term (pintz2023Coeff X) rho n‖ ≤
      (n.divisors.card : ℝ) / (n : ℝ) ^ (1 - eta) := by
  have hre : ((1 - eta : ℝ) : ℂ).re ≤ rho.re := by simpa using hrho
  calc
    ‖LSeries.term (pintz2023Coeff X) rho n‖ ≤
        ‖LSeries.term (pintz2023Coeff X)
          ((1 - eta : ℝ) : ℂ) n‖ :=
      LSeries.norm_term_le_of_re_le_re (pintz2023Coeff X) hre n
    _ = ‖pintz2023Coeff X n‖ / (n : ℝ) ^ (1 - eta) := by
      rw [LSeries.norm_term_eq]
      simp [hn.ne']
    _ ≤ (n.divisors.card : ℝ) / (n : ℝ) ^ (1 - eta) := by
      exact div_le_div_of_nonneg_right
        (norm_pintz2023Coeff_le_divisors_card X n) (by positivity)

/-- Pointwise equation-(4.3) estimate, with the divisor exponent and its
uniform constant explicit. -/
theorem norm_pintz2023WeightedTerm_le_pseries
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X n : ℕ} {rho : ℂ} {eta lambda : ℝ},
        1 - eta ≤ rho.re → 3 ≤ lambda → 0 < n →
        ‖pintz2023WeightedTerm X rho lambda n‖ ≤
          (C * Real.exp (lambda + lambda ^ 2) *
            Real.sqrt (Real.pi / (1 / lambda))) *
              (1 / (n : ℝ) ^ (lambda + 1 - eta - delta)) := by
  obtain ⟨C, hC, hdiv⟩ := divisorCountBound_native delta hdelta
  refine ⟨C, hC, ?_⟩
  intro X n rho eta lambda hrho hlambda hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoeff := norm_pintz2023_LSeries_term_le
    (X := X) hrho hn
  have hweight := norm_pintz2023GaussianWeight_le hlambda hn
  rw [pintz_shifted_exponential_eq_rpow hn] at hweight
  rw [pintz2023WeightedTerm, norm_mul]
  calc
    ‖LSeries.term (pintz2023Coeff X) rho n‖ *
          ‖pintz2023GaussianWeight lambda n‖ ≤
        ((n.divisors.card : ℝ) / (n : ℝ) ^ (1 - eta)) *
          ((Real.exp (lambda + lambda ^ 2) / (n : ℝ) ^ lambda) *
            Real.sqrt (Real.pi / (1 / lambda))) :=
      mul_le_mul hcoeff hweight (norm_nonneg _) (by positivity)
    _ ≤ ((C * (n : ℝ) ^ delta) / (n : ℝ) ^ (1 - eta)) *
          ((Real.exp (lambda + lambda ^ 2) / (n : ℝ) ^ lambda) *
            Real.sqrt (Real.pi / (1 / lambda))) := by
      gcongr
      exact hdiv n hn
    _ = (C * Real.exp (lambda + lambda ^ 2) *
            Real.sqrt (Real.pi / (1 / lambda))) *
          (1 / (n : ℝ) ^ (lambda + 1 - eta - delta)) := by
      rw [show lambda + 1 - eta - delta =
        (1 - eta) + lambda - delta by ring_nf]
      have hpow : (n : ℝ) ^ ((1 - eta) + lambda - delta) =
          ((n : ℝ) ^ (1 - eta) * (n : ℝ) ^ lambda) /
            (n : ℝ) ^ delta := by
        rw [Real.rpow_sub hnReal, Real.rpow_add hnReal]
      rw [hpow]
      field_simp

/-- Free-line version of the pointwise tail bound, retaining the useful
`1/q` supplied by the denominator on `Re s = q`. -/
theorem norm_pintz2023WeightedTerm_le_pseries_on_line
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X n : ℕ} {rho : ℂ} {eta lambda q : ℝ},
        1 - eta ≤ rho.re → 0 < lambda → 3 ≤ q → 0 < n →
        ‖pintz2023WeightedTerm X rho lambda n‖ ≤
          ((C / q) * Real.exp (q ^ 2 / lambda + lambda * q) *
            Real.sqrt (Real.pi / (1 / lambda))) *
              (1 / (n : ℝ) ^ (q + 1 - eta - delta)) := by
  obtain ⟨C, hC, hdiv⟩ := divisorCountBound_native delta hdelta
  refine ⟨C, hC, ?_⟩
  intro X n rho eta lambda q hrho hlambda hq hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoeff := norm_pintz2023_LSeries_term_le
    (X := X) hrho hn
  have hweight := norm_pintz2023GaussianWeight_le_on_line_div
    (lambda := lambda) (q := q) hlambda hq hn
  rw [pintz2023WeightedTerm, norm_mul]
  calc
    ‖LSeries.term (pintz2023Coeff X) rho n‖ *
          ‖pintz2023GaussianWeight lambda n‖ ≤
        ((n.divisors.card : ℝ) / (n : ℝ) ^ (1 - eta)) *
          ((1 / q) *
            (Real.exp (q ^ 2 / lambda + lambda * q) / (n : ℝ) ^ q) *
              Real.sqrt (Real.pi / (1 / lambda))) :=
      mul_le_mul hcoeff hweight (norm_nonneg _) (by positivity)
    _ ≤ ((C * (n : ℝ) ^ delta) / (n : ℝ) ^ (1 - eta)) *
          ((1 / q) *
            (Real.exp (q ^ 2 / lambda + lambda * q) / (n : ℝ) ^ q) *
              Real.sqrt (Real.pi / (1 / lambda))) := by
      gcongr
      exact hdiv n hn
    _ = ((C / q) * Real.exp (q ^ 2 / lambda + lambda * q) *
            Real.sqrt (Real.pi / (1 / lambda))) *
          (1 / (n : ℝ) ^ (q + 1 - eta - delta)) := by
      rw [show q + 1 - eta - delta =
        (1 - eta) + q - delta by ring_nf]
      have hpow : (n : ℝ) ^ ((1 - eta) + q - delta) =
          ((n : ℝ) ^ (1 - eta) * (n : ℝ) ^ q) /
            (n : ℝ) ^ delta := by
        rw [Real.rpow_sub hnReal, Real.rpow_add hnReal]
      rw [hpow]
      field_simp

/-- Tail comparison with the fixed convergent `9/8` p-series. -/
theorem pintz2023_tail_pseries_pointwise_nine_eighth
    {lambda q eta delta : ℝ} {n : ℕ}
    (hgap : 0 ≤ q + 1 - eta - delta - 9 / 8)
    (hn : pintz2023Cutoff lambda < n) :
    1 / (n : ℝ) ^ (q + 1 - eta - delta) ≤
      Real.exp (-(lambda + 3) *
        (q + 1 - eta - delta - 9 / 8)) *
        ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (9 / 8 : ℂ) n‖ := by
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hbase := pintz2023Cutoff_lt_cast hn
  have hpow :
      Real.exp (lambda + 3) ^
          (q + 1 - eta - delta - 9 / 8) ≤
        (n : ℝ) ^ (q + 1 - eta - delta - 9 / 8) :=
    Real.rpow_le_rpow (Real.exp_pos _).le hbase.le hgap
  have hleft :
      Real.exp (lambda + 3) ^
          (q + 1 - eta - delta - 9 / 8) =
        Real.exp ((lambda + 3) *
          (q + 1 - eta - delta - 9 / 8)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hinv :
      1 / (n : ℝ) ^ (q + 1 - eta - delta - 9 / 8) ≤
        Real.exp (-(lambda + 3) *
          (q + 1 - eta - delta - 9 / 8)) := by
    calc
      1 / (n : ℝ) ^ (q + 1 - eta - delta - 9 / 8) ≤
          1 / (Real.exp (lambda + 3) ^
            (q + 1 - eta - delta - 9 / 8)) :=
        one_div_le_one_div_of_le (by positivity) hpow
      _ = Real.exp (-(lambda + 3) *
          (q + 1 - eta - delta - 9 / 8)) := by
        rw [hleft, one_div, ← Real.exp_neg]
        congr 1
        ring_nf
  have hnormTerm :
      ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (9 / 8 : ℂ) n‖ =
        1 / (n : ℝ) ^ (9 / 8 : ℝ) := by
    rw [LSeries.norm_term_eq]
    simp only [if_neg hnPos.ne', norm_one]
    norm_num
  rw [hnormTerm]
  rw [show q + 1 - eta - delta = (9 / 8 : ℝ) +
      (q + 1 - eta - delta - 9 / 8) by ring_nf]
  rw [Real.rpow_add hnReal]
  calc
    1 / ((n : ℝ) ^ (9 / 8 : ℝ) *
        (n : ℝ) ^ (q + 1 - eta - delta - 9 / 8)) =
        (1 / (n : ℝ) ^ (9 / 8 : ℝ)) *
          (1 / (n : ℝ) ^ (q + 1 - eta - delta - 9 / 8)) := by
      field_simp
    _ ≤ (1 / (n : ℝ) ^ (9 / 8 : ℝ)) *
        Real.exp (-(lambda + 3) *
          (q + 1 - eta - delta - 9 / 8)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring_nf

theorem pintz2023_optimized_line_sqrt_factor_le_one
    {lambda : ℝ} (hlambda : 8 ≤ lambda) :
    (1 / (3 * lambda / 2)) *
        Real.sqrt (Real.pi / (1 / lambda)) ≤ 1 := by
  have hlambdaPos : 0 < lambda := by linarith
  have hqPos : 0 < 3 * lambda / 2 := by positivity
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hinside : Real.pi / (1 / lambda) = Real.pi * lambda := by
    field_simp
  have hrad : 0 ≤ Real.pi / (1 / lambda) := by positivity
  have hsquare : (Real.sqrt (Real.pi / (1 / lambda))) ^ 2 =
      Real.pi / (1 / lambda) := (Real.sq_sqrt hrad)
  have hqSquare : Real.pi / (1 / lambda) ≤ (3 * lambda / 2) ^ 2 := by
    rw [hinside]
    nlinarith
  have hsqrt : Real.sqrt (Real.pi / (1 / lambda)) ≤
      3 * lambda / 2 := by
    nlinarith [Real.sqrt_nonneg (Real.pi / (1 / lambda))]
  calc
    (1 / (3 * lambda / 2)) *
        Real.sqrt (Real.pi / (1 / lambda)) ≤
      (1 / (3 * lambda / 2)) * (3 * lambda / 2) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 1 := by field_simp

theorem pintz2023_optimized_line_exponent_le
    {lambda eta : ℝ} (hlambda : 8 ≤ lambda) (heta : eta ≤ 1 / 24) :
    (3 * lambda / 2) ^ 2 / lambda + lambda * (3 * lambda / 2) -
        (lambda + 3) *
          (3 * lambda / 2 + 1 - eta - 1 / 48 - 9 / 8) ≤
      -2 * lambda + 1 / 16 := by
  have hprod : eta * (lambda + 3) ≤ (1 / 24) * (lambda + 3) :=
    mul_le_mul_of_nonneg_right heta (by linarith)
  have hlambdaNe : lambda ≠ 0 := by linarith
  field_simp [hlambdaNe]
  nlinarith

theorem pintz2023_optimized_line_exponential_le
    {lambda eta : ℝ} (hlambda : 8 ≤ lambda) (heta : eta ≤ 1 / 24) :
    Real.exp ((3 * lambda / 2) ^ 2 / lambda +
        lambda * (3 * lambda / 2)) *
      Real.exp (-(lambda + 3) *
        (3 * lambda / 2 + 1 - eta - 1 / 48 - 9 / 8)) ≤
      Real.exp (1 / 16) * Real.exp (-2 * lambda) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := pintz2023_optimized_line_exponent_le hlambda heta
  linarith

theorem summable_norm_nine_eighth_LSeries_term :
    Summable (fun n : ℕ =>
      ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (9 / 8 : ℂ) n‖) := by
  apply summable_norm_iff.mpr
  exact LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (by intro n hn; simp) (by norm_num)

noncomputable def pintz2023NineEighthMass : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (9 / 8 : ℂ) n‖

theorem pintz2023NineEighthMass_nonneg :
    0 ≤ pintz2023NineEighthMass :=
  tsum_nonneg (fun _ => norm_nonneg _)

/-- Pintz equation (4.6), for the literal finite-mollifier tail.  The
constant is uniform in `X`, the zero `rho`, `eta`, and `lambda`; its only
arithmetic input is the fixed `1/48` divisor bound. -/
theorem norm_tsum_pintz2023TailTerm_le_exp_neg_two
    : ∃ K : ℝ, 0 < K ∧
      ∀ {X : ℕ} {rho : ℂ} {eta lambda : ℝ},
        1 - eta ≤ rho.re → 8 ≤ lambda → eta ≤ 1 / 24 →
        ‖∑' n : ℕ, pintz2023TailTerm X rho lambda n‖ ≤
          K * Real.exp (-2 * lambda) := by
  obtain ⟨C, hC, hline⟩ :=
    norm_pintz2023WeightedTerm_le_pseries_on_line
      (delta := 1 / 48) (by norm_num)
  let K : ℝ := C * Real.exp (1 / 16) *
    (pintz2023NineEighthMass + 1)
  have hK : 0 < K := by
    dsimp [K]
    have hmass := pintz2023NineEighthMass_nonneg
    positivity
  refine ⟨K, hK, ?_⟩
  intro X rho eta lambda hrho hlambda heta
  let q : ℝ := 3 * lambda / 2
  let D : ℝ := C * Real.exp (1 / 16) * Real.exp (-2 * lambda)
  have hlambdaPos : 0 < lambda := by linarith
  have hq : 3 ≤ q := by
    dsimp [q]
    linarith
  have hsqrt : (1 / q) * Real.sqrt (Real.pi / (1 / lambda)) ≤ 1 := by
    simpa [q] using pintz2023_optimized_line_sqrt_factor_le_one hlambda
  have hexp :
      Real.exp (q ^ 2 / lambda + lambda * q) *
          Real.exp (-(lambda + 3) *
            (q + 1 - eta - 1 / 48 - 9 / 8)) ≤
        Real.exp (1 / 16) * Real.exp (-2 * lambda) := by
    simpa [q] using pintz2023_optimized_line_exponential_le hlambda heta
  have hmajor := summable_norm_nine_eighth_LSeries_term.mul_left D
  have hpoint : ∀ n : ℕ,
      ‖pintz2023TailTerm X rho lambda n‖ ≤
        D * ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (9 / 8 : ℂ) n‖ := by
    intro n
    by_cases hn : pintz2023Cutoff lambda < n
    · have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
      have hraw := hline (X := X) (n := n) (rho := rho)
        (eta := eta) (lambda := lambda) (q := q)
        hrho hlambdaPos hq hnPos
      have hgap : 0 ≤ q + 1 - eta - 1 / 48 - 9 / 8 := by
        dsimp [q]
        linarith
      have hp := pintz2023_tail_pseries_pointwise_nine_eighth
        (lambda := lambda) (q := q) (eta := eta) (delta := 1 / 48)
        hgap hn
      rw [pintz2023TailTerm, if_pos hn]
      calc
        ‖pintz2023WeightedTerm X rho lambda n‖ ≤
            ((C / q) * Real.exp (q ^ 2 / lambda + lambda * q) *
              Real.sqrt (Real.pi / (1 / lambda))) *
                (1 / (n : ℝ) ^ (q + 1 - eta - 1 / 48)) := hraw
        _ ≤ ((C / q) * Real.exp (q ^ 2 / lambda + lambda * q) *
              Real.sqrt (Real.pi / (1 / lambda))) *
            (Real.exp (-(lambda + 3) *
                (q + 1 - eta - 1 / 48 - 9 / 8)) *
              ‖LSeries.term (fun _ : ℕ => (1 : ℂ))
                (9 / 8 : ℂ) n‖) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = (C * ((1 / q) *
              Real.sqrt (Real.pi / (1 / lambda))) *
            (Real.exp (q ^ 2 / lambda + lambda * q) *
              Real.exp (-(lambda + 3) *
                (q + 1 - eta - 1 / 48 - 9 / 8)))) *
              ‖LSeries.term (fun _ : ℕ => (1 : ℂ))
                (9 / 8 : ℂ) n‖ := by ring
        _ ≤ (C * 1 *
            (Real.exp (1 / 16) * Real.exp (-2 * lambda))) *
              ‖LSeries.term (fun _ : ℕ => (1 : ℂ))
                (9 / 8 : ℂ) n‖ := by
          gcongr
        _ = D * ‖LSeries.term (fun _ : ℕ => (1 : ℂ))
              (9 / 8 : ℂ) n‖ := by
          dsimp [D]
          ring
    · rw [pintz2023TailTerm, if_neg hn, norm_zero]
      exact mul_nonneg (by
        dsimp [D]
        positivity) (norm_nonneg _)
  have htailNorm : Summable (fun n : ℕ =>
      ‖pintz2023TailTerm X rho lambda n‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  calc
    ‖∑' n : ℕ, pintz2023TailTerm X rho lambda n‖ ≤
        ∑' n : ℕ, ‖pintz2023TailTerm X rho lambda n‖ :=
      norm_tsum_le_tsum_norm htailNorm
    _ ≤ ∑' n : ℕ, D *
          ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) (9 / 8 : ℂ) n‖ :=
      htailNorm.tsum_le_tsum hpoint hmajor
    _ = D * pintz2023NineEighthMass := by
      rw [tsum_mul_left]
      rfl
    _ ≤ D * (pintz2023NineEighthMass + 1) := by
      gcongr
      linarith [pintz2023NineEighthMass_nonneg]
    _ = K * Real.exp (-2 * lambda) := by
      dsimp [D, K]
      ring

/-- Absolute summability of the literal source tail.  The quantitative
cutoff estimate is proved below this structural fact. -/
theorem summable_norm_pintz2023TailTerm
    {X : ℕ} {rho : ℂ} {eta lambda : ℝ}
    (hrho : 1 - eta ≤ rho.re) (hlambda : 8 ≤ lambda)
    (heta : eta ≤ 1 / 4) :
    Summable (fun n : ℕ => ‖pintz2023TailTerm X rho lambda n‖) := by
  obtain ⟨C, hC, hpoint⟩ :=
    norm_pintz2023WeightedTerm_le_pseries (delta := 1 / 4) (by norm_num)
  let K : ℝ := C * Real.exp (lambda + lambda ^ 2) *
    Real.sqrt (Real.pi / (1 / lambda))
  have hp : 1 < lambda + 1 - eta - 1 / 4 := by linarith
  have hs : Summable (fun n : ℕ =>
      1 / (n : ℝ) ^ (lambda + 1 - eta - 1 / 4)) :=
    by simpa [one_div] using (Real.summable_nat_rpow_inv.mpr hp)
  refine (hs.mul_left K).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  by_cases hn : pintz2023Cutoff lambda < n
  · rw [pintz2023TailTerm, if_pos hn]
    exact hpoint hrho (by linarith) (lt_of_le_of_lt (Nat.zero_le _) hn)
  · rw [pintz2023TailTerm, if_neg hn, norm_zero]
    positivity

#print axioms norm_pintz2023_LSeries_term_le
#print axioms norm_pintz2023WeightedTerm_le_pseries
#print axioms norm_pintz2023WeightedTerm_le_pseries_on_line
#print axioms pintz2023_tail_pseries_pointwise_nine_eighth
#print axioms summable_norm_pintz2023TailTerm
#print axioms norm_tsum_pintz2023TailTerm_le_exp_neg_two

end

end GafniTao
