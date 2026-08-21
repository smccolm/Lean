import RiemannZeta.GuthMaynard.HughesYoungGammaRatioJets

open Complex Filter Set Topology
open Classical
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Sharp fixed-shift Gamma ratio for the Hughes--Young central residue

The moving pole in the equation-(84) contour shift fixes the Mellin
variable at `W = 1/2`.  At that point the four real Gamma factors have a
genuine conductor cost of exactly one power of the physical height.  A
generic horizontal-strip estimate loses this exponent.  The finite Euler
product comparison below retains it.
-/

/-- The one-step rational inequality behind the telescoping Euler-product
bound.  Its small `1 + x⁻²` loss has a convergent product. -/
theorem gammaQuarterHalf_step_le
    {x y : ℝ} (hx : 1 ≤ x) :
    ((((x + 1 / 4) ^ 2 + y ^ 2) /
          ((x + 1 / 2) ^ 2 + y ^ 2)) ^ 4) ≤
      ((x ^ 2 + y ^ 2) / ((x + 1) ^ 2 + y ^ 2)) *
        (1 + x⁻¹ ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hA : 0 < (x + 1 / 2) ^ 2 + y ^ 2 := by positivity
  have hB : 0 < (x + 1) ^ 2 + y ^ 2 := by positivity
  have hC : 0 < x ^ 2 := sq_pos_of_pos hx0
  rw [div_pow]
  rw [div_le_iff₀ (pow_pos hA 4)]
  rw [mul_assoc, div_eq_mul_inv, inv_pow]
  rw [show 1 + (x ^ 2)⁻¹ = (x ^ 2 + 1) / x ^ 2 by
    field_simp [hx0.ne']]
  rw [show
      (x ^ 2 + y ^ 2) / ((x + 1) ^ 2 + y ^ 2) *
          ((x ^ 2 + 1) / x ^ 2 * ((x + 1 / 2) ^ 2 + y ^ 2) ^ 4) =
        ((x ^ 2 + y ^ 2) * (x ^ 2 + 1) *
          ((x + 1 / 2) ^ 2 + y ^ 2) ^ 4) /
            (((x + 1) ^ 2 + y ^ 2) * x ^ 2) by
      field_simp [hx0.ne']]
  rw [le_div_iff₀ (mul_pos hB hC)]
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- The corresponding one-step comparison for the full quarter-to-three-
quarter displacement.  Squaring the quotient records the half-power
conductor cost, while the same summable Euler-product loss is sufficient. -/
theorem gammaQuarterThreeQuarter_step_le
    {x y : ℝ} (hx : 1 ≤ x) :
    ((((x + 1 / 4) ^ 2 + y ^ 2) /
          ((x + 3 / 4) ^ 2 + y ^ 2)) ^ 2) ≤
      ((x ^ 2 + y ^ 2) / ((x + 1) ^ 2 + y ^ 2)) *
        (1 + x⁻¹ ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hA : 0 < (x + 3 / 4) ^ 2 + y ^ 2 := by positivity
  have hB : 0 < (x + 1) ^ 2 + y ^ 2 := by positivity
  have hC : 0 < x ^ 2 := sq_pos_of_pos hx0
  rw [div_pow]
  rw [div_le_iff₀ (pow_pos hA 2)]
  rw [mul_assoc, div_eq_mul_inv, inv_pow]
  rw [show 1 + (x ^ 2)⁻¹ = (x ^ 2 + 1) / x ^ 2 by
    field_simp [hx0.ne']]
  rw [show
      (x ^ 2 + y ^ 2) / ((x + 1) ^ 2 + y ^ 2) *
          ((x ^ 2 + 1) / x ^ 2 * ((x + 3 / 4) ^ 2 + y ^ 2) ^ 2) =
        ((x ^ 2 + y ^ 2) * (x ^ 2 + 1) *
          ((x + 3 / 4) ^ 2 + y ^ 2) ^ 2) /
            (((x + 1) ^ 2 + y ^ 2) * x ^ 2) by
      field_simp [hx0.ne']]
  rw [le_div_iff₀ (mul_pos hB hC)]
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- The convergent loss in the one-step comparison is uniformly bounded.
The deliberately generous constant keeps the later archimedean estimate
independent of the truncation point. -/
theorem gammaQuarterHalf_errorProduct_le (n : ℕ) :
    ∏ j ∈ Finset.Icc 1 n, (1 + ((j : ℝ)⁻¹) ^ 2) ≤ Real.exp 8 := by
  have hpoint : ∀ j ∈ Finset.Icc 1 n,
      1 + ((j : ℝ)⁻¹) ^ 2 ≤
        Real.exp (4 * (1 / (((j : ℝ) + 1) ^ 2))) := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by
      exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hj0 : (0 : ℝ) < j := zero_lt_one.trans_le hj1
    have hden : 0 < ((j : ℝ) + 1) ^ 2 := sq_pos_of_pos (by positivity)
    have hinv : ((j : ℝ)⁻¹) ^ 2 ≤ 4 * (1 / (((j : ℝ) + 1) ^ 2)) := by
      rw [inv_pow]
      have hmul : 0 < (j : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2) :=
        mul_pos (sq_pos_of_pos hj0) hden
      rw [← mul_le_mul_iff_of_pos_left hmul]
      field_simp [hj0.ne']
      nlinarith
    calc
      1 + ((j : ℝ)⁻¹) ^ 2 ≤
          4 * (1 / (((j : ℝ) + 1) ^ 2)) + 1 := by linarith
      _ ≤ Real.exp (4 * (1 / (((j : ℝ) + 1) ^ 2))) :=
        Real.add_one_le_exp _
  calc
    ∏ j ∈ Finset.Icc 1 n, (1 + ((j : ℝ)⁻¹) ^ 2)
        ≤ ∏ j ∈ Finset.Icc 1 n,
            Real.exp (4 * (1 / (((j : ℝ) + 1) ^ 2))) := by
          exact Finset.prod_le_prod (fun _ _ => by positivity) hpoint
    _ = Real.exp
          (∑ j ∈ Finset.Icc 1 n, 4 * (1 / (((j : ℝ) + 1) ^ 2))) := by
          rw [← Real.exp_sum]
    _ ≤ Real.exp 8 := by
      apply Real.exp_le_exp.mpr
      calc
        ∑ j ∈ Finset.Icc 1 n, 4 * (1 / (((j : ℝ) + 1) ^ 2))
            ≤ 4 * ∑' j : ℕ, 1 / (((j : ℝ) + 1) ^ 2) := by
              rw [← Finset.mul_sum]
              apply mul_le_mul_of_nonneg_left
                (Complex.summable_one_div_natCast_add_one_sq.sum_le_tsum
                  (Finset.Icc 1 n) (fun j _ => by positivity))
                (by norm_num)
        _ ≤ 8 := by
          have hs := Complex.summable_one_div_natCast_add_one_sq
          rw [hs.tsum_eq_zero_add]
          have htail := Complex.tsum_one_div_natCast_add_add_one_sq_le
            (N := 1) (by norm_num)
          norm_num at htail ⊢
          linarith

/-- The rational part of the finite product telescopes exactly. -/
theorem gammaQuarterHalf_telescope (n : ℕ) (y : ℝ) :
    ∏ j ∈ Finset.Icc 1 n,
        (((j : ℝ) ^ 2 + y ^ 2) / (((j : ℝ) + 1) ^ 2 + y ^ 2)) =
      (1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2) := by
  induction n with
  | zero =>
      norm_num
      field_simp
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        rw [Finset.prod_Icc_succ_top (by omega), ih]
        have hden : 0 < ((n : ℝ) + 1) ^ 2 + y ^ 2 := by positivity
        field_simp [hden.ne']
        push_cast
        ring

/-- Product form of the sharp quarter-to-half Gamma comparison. -/
theorem gammaQuarterHalf_product_le (n : ℕ) (y : ℝ) :
    (∏ j ∈ Finset.Icc 1 n,
        ((((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) /
          (((j : ℝ) + 1 / 2) ^ 2 + y ^ 2)) ^ 4) ≤
      Real.exp 8 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      (((((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) /
          (((j : ℝ) + 1 / 2) ^ 2 + y ^ 2)) ^ 4) ≤
        (((j : ℝ) ^ 2 + y ^ 2) /
          (((j : ℝ) + 1) ^ 2 + y ^ 2)) *
          (1 + ((j : ℝ)⁻¹) ^ 2) := by
    intro j hj
    exact gammaQuarterHalf_step_le (by
      exact_mod_cast (Finset.mem_Icc.mp hj).1)
  calc
    _ ≤ ∏ j ∈ Finset.Icc 1 n,
        ((((j : ℝ) ^ 2 + y ^ 2) /
          (((j : ℝ) + 1) ^ 2 + y ^ 2)) *
          (1 + ((j : ℝ)⁻¹) ^ 2)) := by
            exact Finset.prod_le_prod (fun _ _ => by positivity) hstep
    _ = ((∏ j ∈ Finset.Icc 1 n,
          (((j : ℝ) ^ 2 + y ^ 2) /
            (((j : ℝ) + 1) ^ 2 + y ^ 2))) *
        (∏ j ∈ Finset.Icc 1 n, (1 + ((j : ℝ)⁻¹) ^ 2))) := by
          simp only [Finset.prod_mul_distrib]
    _ ≤ ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) *
          Real.exp 8 := by
          have htel := gammaQuarterHalf_telescope n y
          rw [htel]
          exact mul_le_mul_of_nonneg_left (gammaQuarterHalf_errorProduct_le n)
            (by positivity)
    _ = Real.exp 8 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by ring

/-- Product form of the sharp quarter-to-three-quarter Gamma comparison. -/
theorem gammaQuarterThreeQuarter_product_le (n : ℕ) (y : ℝ) :
    (∏ j ∈ Finset.Icc 1 n,
        ((((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) /
          (((j : ℝ) + 3 / 4) ^ 2 + y ^ 2)) ^ 2) ≤
      Real.exp 8 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      (((((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) /
          (((j : ℝ) + 3 / 4) ^ 2 + y ^ 2)) ^ 2) ≤
        (((j : ℝ) ^ 2 + y ^ 2) /
          (((j : ℝ) + 1) ^ 2 + y ^ 2)) *
          (1 + ((j : ℝ)⁻¹) ^ 2) := by
    intro j hj
    exact gammaQuarterThreeQuarter_step_le (by
      exact_mod_cast (Finset.mem_Icc.mp hj).1)
  calc
    _ ≤ ∏ j ∈ Finset.Icc 1 n,
        ((((j : ℝ) ^ 2 + y ^ 2) /
          (((j : ℝ) + 1) ^ 2 + y ^ 2)) *
          (1 + ((j : ℝ)⁻¹) ^ 2)) := by
            exact Finset.prod_le_prod (fun _ _ => by positivity) hstep
    _ = ((∏ j ∈ Finset.Icc 1 n,
          (((j : ℝ) ^ 2 + y ^ 2) /
            (((j : ℝ) + 1) ^ 2 + y ^ 2))) *
        (∏ j ∈ Finset.Icc 1 n, (1 + ((j : ℝ)⁻¹) ^ 2))) := by
          simp only [Finset.prod_mul_distrib]
    _ ≤ ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) *
          Real.exp 8 := by
          rw [gammaQuarterHalf_telescope]
          exact mul_le_mul_of_nonneg_left (gammaQuarterHalf_errorProduct_le n)
            (by positivity)
    _ = Real.exp 8 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by ring

private noncomputable def gammaQuarterTerm (j : ℕ) (y : ℝ) : ℝ :=
  ((j : ℝ) + 1 / 4) ^ 2 + y ^ 2

private noncomputable def gammaHalfTerm (j : ℕ) (y : ℝ) : ℝ :=
  ((j : ℝ) + 1 / 2) ^ 2 + y ^ 2

private noncomputable def gammaThreeQuarterTerm (j : ℕ) (y : ℝ) : ℝ :=
  ((j : ℝ) + 3 / 4) ^ 2 + y ^ 2

private theorem gammaQuarterTerm_pos (j : ℕ) (y : ℝ) :
    0 < gammaQuarterTerm j y := by
  unfold gammaQuarterTerm
  positivity

private theorem gammaHalfTerm_pos (j : ℕ) (y : ℝ) :
    0 < gammaHalfTerm j y := by
  unfold gammaHalfTerm
  positivity

private theorem gammaThreeQuarterTerm_pos (j : ℕ) (y : ℝ) :
    0 < gammaThreeQuarterTerm j y := by
  unfold gammaThreeQuarterTerm
  positivity

private theorem gamma_sqrt_product_ratio_pow_eight (n : ℕ) (y : ℝ) :
    ((∏ j ∈ Finset.range (n + 1), Real.sqrt (gammaQuarterTerm j y)) /
        (∏ j ∈ Finset.range (n + 1), Real.sqrt (gammaHalfTerm j y))) ^ 8 =
      ∏ j ∈ Finset.range (n + 1),
        (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4 := by
  rw [div_pow]
  simp_rw [← Finset.prod_pow]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hq := (gammaQuarterTerm_pos j y).le
  have hh := (gammaHalfTerm_pos j y).le
  rw [show Real.sqrt (gammaQuarterTerm j y) ^ 8 =
      (Real.sqrt (gammaQuarterTerm j y) ^ 2) ^ 4 by ring,
    show Real.sqrt (gammaHalfTerm j y) ^ 8 =
      (Real.sqrt (gammaHalfTerm j y) ^ 2) ^ 4 by ring,
    Real.sq_sqrt hq, Real.sq_sqrt hh, div_pow]

private theorem gammaQuarterHalf_rangeProduct_le (n : ℕ) (y : ℝ) :
    ∏ j ∈ Finset.range (n + 1),
        (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4 ≤
      Real.exp 8 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
  have hsplit := Finset.prod_range_eq_mul_Ico
    (f := fun j : ℕ => (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4)
    (n := n + 1) (by omega)
  rw [Finset.Ico_add_one_right_eq_Icc] at hsplit
  rw [hsplit]
  have hzero :
      (gammaQuarterTerm 0 y / gammaHalfTerm 0 y) ^ 4 ≤ 1 := by
    have hq : gammaQuarterTerm 0 y ≤ gammaHalfTerm 0 y := by
      unfold gammaQuarterTerm gammaHalfTerm
      nlinarith
    have hratio : gammaQuarterTerm 0 y / gammaHalfTerm 0 y ≤ 1 := by
      rw [div_le_one (gammaHalfTerm_pos 0 y)]
      exact hq
    have hnonneg : 0 ≤ gammaQuarterTerm 0 y / gammaHalfTerm 0 y :=
      div_nonneg (gammaQuarterTerm_pos 0 y).le (gammaHalfTerm_pos 0 y).le
    exact pow_le_one₀ hnonneg hratio
  have htail :
      ∏ j ∈ Finset.Icc 1 n,
          (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4 ≤
        Real.exp 8 *
          ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
    simpa only [gammaQuarterTerm, gammaHalfTerm] using
      gammaQuarterHalf_product_le n y
  calc
    (gammaQuarterTerm 0 y / gammaHalfTerm 0 y) ^ 4 *
        ∏ j ∈ Finset.Icc 1 n,
          (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4
        ≤ 1 * ∏ j ∈ Finset.Icc 1 n,
          (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4 := by
            gcongr
    _ ≤ Real.exp 8 *
          ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
            simpa using htail

private theorem gamma_sqrt_product_ratio_quarter_threeQuarter_pow_four
    (n : ℕ) (y : ℝ) :
    ((∏ j ∈ Finset.range (n + 1), Real.sqrt (gammaQuarterTerm j y)) /
        (∏ j ∈ Finset.range (n + 1),
          Real.sqrt (gammaThreeQuarterTerm j y))) ^ 4 =
      ∏ j ∈ Finset.range (n + 1),
        (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2 := by
  rw [div_pow]
  simp_rw [← Finset.prod_pow]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hq := (gammaQuarterTerm_pos j y).le
  have ht := (gammaThreeQuarterTerm_pos j y).le
  rw [show Real.sqrt (gammaQuarterTerm j y) ^ 4 =
      (Real.sqrt (gammaQuarterTerm j y) ^ 2) ^ 2 by ring,
    show Real.sqrt (gammaThreeQuarterTerm j y) ^ 4 =
      (Real.sqrt (gammaThreeQuarterTerm j y) ^ 2) ^ 2 by ring,
    Real.sq_sqrt hq, Real.sq_sqrt ht, div_pow]

private theorem gammaQuarterThreeQuarter_rangeProduct_le (n : ℕ) (y : ℝ) :
    ∏ j ∈ Finset.range (n + 1),
        (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2 ≤
      Real.exp 8 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
  have hsplit := Finset.prod_range_eq_mul_Ico
    (f := fun j : ℕ =>
      (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2)
    (n := n + 1) (by omega)
  rw [Finset.Ico_add_one_right_eq_Icc] at hsplit
  rw [hsplit]
  have hzero :
      (gammaQuarterTerm 0 y / gammaThreeQuarterTerm 0 y) ^ 2 ≤ 1 := by
    have hqt : gammaQuarterTerm 0 y ≤ gammaThreeQuarterTerm 0 y := by
      unfold gammaQuarterTerm gammaThreeQuarterTerm
      nlinarith
    have hratio : gammaQuarterTerm 0 y / gammaThreeQuarterTerm 0 y ≤ 1 := by
      rw [div_le_one (gammaThreeQuarterTerm_pos 0 y)]
      exact hqt
    exact pow_le_one₀
      (div_nonneg (gammaQuarterTerm_pos 0 y).le
        (gammaThreeQuarterTerm_pos 0 y).le) hratio
  have htail :
      ∏ j ∈ Finset.Icc 1 n,
          (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2 ≤
        Real.exp 8 *
          ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
    simpa only [gammaQuarterTerm, gammaThreeQuarterTerm] using
      gammaQuarterThreeQuarter_product_le n y
  calc
    (gammaQuarterTerm 0 y / gammaThreeQuarterTerm 0 y) ^ 2 *
        ∏ j ∈ Finset.Icc 1 n,
          (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2
        ≤ 1 * ∏ j ∈ Finset.Icc 1 n,
          (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2 := by
            gcongr
    _ ≤ Real.exp 8 *
          ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by
            simpa using htail

/-- The sharp quotient estimate at the finite Euler-product level. -/
theorem norm_GammaSeq_half_div_quarter_pow_eight_le
    (y : ℝ) {n : ℕ} (hn : 0 < n) :
    (‖Complex.GammaSeq ((1 / 2 : ℂ) + (y : ℂ) * I) n‖ /
        ‖Complex.GammaSeq ((1 / 4 : ℂ) + (y : ℂ) * I) n‖) ^ 8 ≤
      Real.exp 8 * (1 + y ^ 2) := by
  let N : ℝ := n
  let F : ℝ := n.factorial
  let Dq : ℝ := ∏ j ∈ Finset.range (n + 1),
    Real.sqrt (((1 / 4 : ℝ) + j) ^ 2 + y ^ 2)
  let Dh : ℝ := ∏ j ∈ Finset.range (n + 1),
    Real.sqrt (((1 / 2 : ℝ) + j) ^ 2 + y ^ 2)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hF : 0 < F := by
    dsimp [F]
    exact_mod_cast Nat.factorial_pos n
  have hDq : 0 < Dq := by
    dsimp [Dq]
    apply Finset.prod_pos
    intro j hj
    exact Real.sqrt_pos.2 (by positivity)
  have hDh : 0 < Dh := by
    dsimp [Dh]
    apply Finset.prod_pos
    intro j hj
    exact Real.sqrt_pos.2 (by positivity)
  have hsqrt : (Dq / Dh) ^ 8 =
      ∏ j ∈ Finset.range (n + 1),
        (gammaQuarterTerm j y / gammaHalfTerm j y) ^ 4 := by
    simpa only [Dq, Dh, gammaQuarterTerm, gammaHalfTerm, add_comm] using
      gamma_sqrt_product_ratio_pow_eight n y
  have hrpow :
      ((N ^ (1 / 2 : ℝ)) / (N ^ (1 / 4 : ℝ))) ^ 8 = N ^ 2 := by
    rw [← Real.rpow_sub hN]
    norm_num
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num [Real.rpow_two]
  have hnormHalf :
      ‖Complex.GammaSeq ((1 / 2 : ℂ) + (y : ℂ) * I) n‖ =
        N ^ (1 / 2 : ℝ) * F / Dh := by
    convert (norm_GammaSeq_vertical (a := (1 / 2 : ℝ)) (y := y) hn) using 1
    all_goals norm_num [N, F, Dh]
  have hnormQuarter :
      ‖Complex.GammaSeq ((1 / 4 : ℂ) + (y : ℂ) * I) n‖ =
        N ^ (1 / 4 : ℝ) * F / Dq := by
    convert (norm_GammaSeq_vertical (a := (1 / 4 : ℝ)) (y := y) hn) using 1
    all_goals norm_num [N, F, Dq]
  rw [hnormHalf, hnormQuarter]
  have halgebra :
      ((N ^ (1 / 2 : ℝ) * F / Dh) /
          (N ^ (1 / 4 : ℝ) * F / Dq)) ^ 8 =
        N ^ 2 * (Dq / Dh) ^ 8 := by
    have hNrq : 0 < N ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN _
    rw [show
        (N ^ (1 / 2 : ℝ) * F / Dh) /
            (N ^ (1 / 4 : ℝ) * F / Dq) =
          (N ^ (1 / 2 : ℝ) / N ^ (1 / 4 : ℝ)) * (Dq / Dh) by
      field_simp [hF.ne', hDq.ne', hDh.ne', hNrq.ne']]
    rw [mul_pow, hrpow]
  rw [halgebra, hsqrt]
  have hprod := gammaQuarterHalf_rangeProduct_le n y
  have hscale :
      N ^ 2 *
          (Real.exp 8 *
            ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2))) ≤
        Real.exp 8 * (1 + y ^ 2) := by
    have hNle : N ^ 2 ≤ ((n : ℝ) + 1) ^ 2 + y ^ 2 := by
      dsimp [N]
      nlinarith [sq_nonneg y]
    have hden : 0 < ((n : ℝ) + 1) ^ 2 + y ^ 2 := by positivity
    have hfrac : N ^ 2 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) ≤
          1 + y ^ 2 := by
      calc
        N ^ 2 * ((1 + y ^ 2) /
            (((n : ℝ) + 1) ^ 2 + y ^ 2)) =
          (1 + y ^ 2) *
            (N ^ 2 / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by ring
        _ ≤ (1 + y ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hden).2 hNle) (by positivity)
        _ = 1 + y ^ 2 := by ring
    nlinarith [Real.exp_pos 8]
  exact (mul_le_mul_of_nonneg_left hprod (sq_nonneg N)).trans hscale

/-- Finite Euler-product estimate for the full quarter-to-three-quarter
Gamma quotient.  Its fourth power has exactly one quadratic conductor
factor. -/
theorem norm_GammaSeq_threeQuarter_div_quarter_pow_four_le
    (y : ℝ) {n : ℕ} (hn : 0 < n) :
    (‖Complex.GammaSeq ((3 / 4 : ℂ) + (y : ℂ) * I) n‖ /
        ‖Complex.GammaSeq ((1 / 4 : ℂ) + (y : ℂ) * I) n‖) ^ 4 ≤
      Real.exp 8 * (1 + y ^ 2) := by
  let N : ℝ := n
  let F : ℝ := n.factorial
  let Dq : ℝ := ∏ j ∈ Finset.range (n + 1),
    Real.sqrt (((1 / 4 : ℝ) + j) ^ 2 + y ^ 2)
  let Dt : ℝ := ∏ j ∈ Finset.range (n + 1),
    Real.sqrt (((3 / 4 : ℝ) + j) ^ 2 + y ^ 2)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hF : 0 < F := by
    dsimp [F]
    exact_mod_cast Nat.factorial_pos n
  have hDq : 0 < Dq := by
    dsimp [Dq]
    apply Finset.prod_pos
    intro j hj
    exact Real.sqrt_pos.2 (by positivity)
  have hDt : 0 < Dt := by
    dsimp [Dt]
    apply Finset.prod_pos
    intro j hj
    exact Real.sqrt_pos.2 (by positivity)
  have hsqrt : (Dq / Dt) ^ 4 =
      ∏ j ∈ Finset.range (n + 1),
        (gammaQuarterTerm j y / gammaThreeQuarterTerm j y) ^ 2 := by
    simpa only [Dq, Dt, gammaQuarterTerm, gammaThreeQuarterTerm, add_comm] using
      gamma_sqrt_product_ratio_quarter_threeQuarter_pow_four n y
  have hrpow :
      ((N ^ (3 / 4 : ℝ)) / (N ^ (1 / 4 : ℝ))) ^ 4 = N ^ 2 := by
    rw [← Real.rpow_sub hN]
    norm_num
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num [Real.rpow_two]
  have hnormThreeQuarter :
      ‖Complex.GammaSeq ((3 / 4 : ℂ) + (y : ℂ) * I) n‖ =
        N ^ (3 / 4 : ℝ) * F / Dt := by
    convert (norm_GammaSeq_vertical (a := (3 / 4 : ℝ)) (y := y) hn) using 1
    all_goals norm_num [N, F, Dt]
  have hnormQuarter :
      ‖Complex.GammaSeq ((1 / 4 : ℂ) + (y : ℂ) * I) n‖ =
        N ^ (1 / 4 : ℝ) * F / Dq := by
    convert (norm_GammaSeq_vertical (a := (1 / 4 : ℝ)) (y := y) hn) using 1
    all_goals norm_num [N, F, Dq]
  rw [hnormThreeQuarter, hnormQuarter]
  have halgebra :
      ((N ^ (3 / 4 : ℝ) * F / Dt) /
          (N ^ (1 / 4 : ℝ) * F / Dq)) ^ 4 =
        N ^ 2 * (Dq / Dt) ^ 4 := by
    have hNrq : 0 < N ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN _
    rw [show
        (N ^ (3 / 4 : ℝ) * F / Dt) /
            (N ^ (1 / 4 : ℝ) * F / Dq) =
          (N ^ (3 / 4 : ℝ) / N ^ (1 / 4 : ℝ)) * (Dq / Dt) by
      field_simp [hF.ne', hDq.ne', hDt.ne', hNrq.ne']]
    rw [mul_pow, hrpow]
  rw [halgebra, hsqrt]
  have hprod := gammaQuarterThreeQuarter_rangeProduct_le n y
  have hscale :
      N ^ 2 *
          (Real.exp 8 *
            ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2))) ≤
        Real.exp 8 * (1 + y ^ 2) := by
    have hNle : N ^ 2 ≤ ((n : ℝ) + 1) ^ 2 + y ^ 2 := by
      dsimp [N]
      nlinarith [sq_nonneg y]
    have hden : 0 < ((n : ℝ) + 1) ^ 2 + y ^ 2 := by positivity
    have hfrac : N ^ 2 *
        ((1 + y ^ 2) / (((n : ℝ) + 1) ^ 2 + y ^ 2)) ≤
          1 + y ^ 2 := by
      calc
        N ^ 2 * ((1 + y ^ 2) /
            (((n : ℝ) + 1) ^ 2 + y ^ 2)) =
          (1 + y ^ 2) *
            (N ^ 2 / (((n : ℝ) + 1) ^ 2 + y ^ 2)) := by ring
        _ ≤ (1 + y ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hden).2 hNle) (by positivity)
        _ = 1 + y ^ 2 := by ring
    nlinarith [Real.exp_pos 8]
  exact (mul_le_mul_of_nonneg_left hprod (sq_nonneg N)).trans hscale

/-- Passing Euler's finite products to the limit gives the sharp fixed-shift
Gamma quotient. -/
theorem norm_Gamma_half_div_quarter_pow_eight_le (y : ℝ) :
    (‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖) ^ 8 ≤
      Real.exp 8 * (1 + y ^ 2) := by
  let zh : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  let zq : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I
  have hqne : Complex.Gamma zq ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    dsimp [zq] at hre
    simp at hre
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hhalf : Tendsto
      (fun n : ℕ => ‖Complex.GammaSeq zh (n + 1)‖) atTop
      (𝓝 ‖Complex.Gamma zh‖) :=
    (Complex.GammaSeq_tendsto_Gamma zh).norm.comp (tendsto_add_atTop_nat 1)
  have hquarter : Tendsto
      (fun n : ℕ => ‖Complex.GammaSeq zq (n + 1)‖) atTop
      (𝓝 ‖Complex.Gamma zq‖) :=
    (Complex.GammaSeq_tendsto_Gamma zq).norm.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto
      (fun n : ℕ => ‖Complex.GammaSeq zh (n + 1)‖ /
        ‖Complex.GammaSeq zq (n + 1)‖) atTop
      (𝓝 (‖Complex.Gamma zh‖ / ‖Complex.Gamma zq‖)) :=
    hhalf.div hquarter (norm_ne_zero_iff.mpr hqne)
  have hleft := hratio.pow 8
  have hright : Tendsto
      (fun _ : ℕ => Real.exp 8 * (1 + y ^ 2)) atTop
      (𝓝 (Real.exp 8 * (1 + y ^ 2))) := tendsto_const_nhds
  change (‖Complex.Gamma zh‖ / ‖Complex.Gamma zq‖) ^ 8 ≤
    Real.exp 8 * (1 + y ^ 2)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  dsimp only [zh, zq]
  exact norm_GammaSeq_half_div_quarter_pow_eight_le y
    (n := n + 1) (by omega)

/-- Sharp quarter-to-three-quarter Gamma quotient.  This is the source-line
archimedean estimate needed by the finite DFI shift completion. -/
theorem norm_Gamma_threeQuarter_div_quarter_pow_four_le (y : ℝ) :
    (‖Complex.Gamma ((3 / 4 : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖) ^ 4 ≤
      Real.exp 8 * (1 + y ^ 2) := by
  let zt : ℂ := (3 / 4 : ℂ) + (y : ℂ) * I
  let zq : ℂ := (1 / 4 : ℂ) + (y : ℂ) * I
  have hqne : Complex.Gamma zq ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    dsimp [zq] at hre
    simp at hre
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hthreeQuarter : Tendsto
      (fun n : ℕ => ‖Complex.GammaSeq zt (n + 1)‖) atTop
      (𝓝 ‖Complex.Gamma zt‖) :=
    (Complex.GammaSeq_tendsto_Gamma zt).norm.comp (tendsto_add_atTop_nat 1)
  have hquarter : Tendsto
      (fun n : ℕ => ‖Complex.GammaSeq zq (n + 1)‖) atTop
      (𝓝 ‖Complex.Gamma zq‖) :=
    (Complex.GammaSeq_tendsto_Gamma zq).norm.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto
      (fun n : ℕ => ‖Complex.GammaSeq zt (n + 1)‖ /
        ‖Complex.GammaSeq zq (n + 1)‖) atTop
      (𝓝 (‖Complex.Gamma zt‖ / ‖Complex.Gamma zq‖)) :=
    hthreeQuarter.div hquarter (norm_ne_zero_iff.mpr hqne)
  have hleft := hratio.pow 4
  have hright : Tendsto
      (fun _ : ℕ => Real.exp 8 * (1 + y ^ 2)) atTop
      (𝓝 (Real.exp 8 * (1 + y ^ 2))) := tendsto_const_nhds
  change (‖Complex.Gamma zt‖ / ‖Complex.Gamma zq‖) ^ 4 ≤
    Real.exp 8 * (1 + y ^ 2)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  dsimp only [zt, zq]
  exact norm_GammaSeq_threeQuarter_div_quarter_pow_four_le y
    (n := n + 1) (by omega)

/-- Fourth-power form of the fixed-shift bound, matching the four Gamma
factors in the Hughes--Young moving residue. -/
theorem norm_Gamma_half_div_quarter_pow_four_le (y : ℝ) :
    (‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖) ^ 4 ≤
      Real.exp 4 * Real.sqrt (1 + y ^ 2) := by
  let r : ℝ :=
    ‖Complex.Gamma ((1 / 2 : ℂ) + (y : ℂ) * I)‖ /
      ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have h8 : r ^ 8 ≤ Real.exp 8 * (1 + y ^ 2) := by
    simpa only [r] using norm_Gamma_half_div_quarter_pow_eight_le y
  have hsqrt : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hexp : Real.exp 8 = (Real.exp 4) ^ 2 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hsquare : (r ^ 4) ^ 2 ≤
      (Real.exp 4 * Real.sqrt (1 + y ^ 2)) ^ 2 := by
    rw [show (r ^ 4) ^ 2 = r ^ 8 by ring, mul_pow, hsqrt, ← hexp]
    exact h8
  exact (sq_le_sq₀ (pow_nonneg hr 4)
    (mul_nonneg (Real.exp_pos 4).le (Real.sqrt_nonneg _))).mp hsquare

private theorem norm_Gamma_vertical_neg_im (a y : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + ((-y : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
  let z : ℂ := (a : ℂ) + ((-y : ℝ) : ℂ) * I
  have hz : star z = (a : ℂ) + (y : ℂ) * I := by simp [z]
  calc
    ‖Complex.Gamma z‖ = ‖star (Complex.Gamma z)‖ := by simp
    _ = ‖Complex.Gamma (star z)‖ :=
      (congrArg norm (Complex.Gamma_conj z)).symm
    _ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by rw [hz]

private theorem norm_GammaR_critical_sharp (y : ℝ) :
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (y : ℂ) * I)‖ =
      Real.pi ^ (-1 / 4 : ℝ) *
        ‖Complex.Gamma ((1 / 4 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  · congr 1
    norm_num
  · congr 2
    push_cast
    ring

private theorem norm_GammaR_one_sharp (y : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) + (y : ℂ) * I)‖ =
      Real.pi ^ (-1 / 2 : ℝ) *
        ‖Complex.Gamma ((1 / 2 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  · congr 1
    norm_num
  · congr 2
    push_cast
    ring

private theorem norm_GammaR_threeHalf_sharp (y : ℝ) :
    ‖Complex.Gammaℝ ((3 / 2 : ℂ) + (y : ℂ) * I)‖ =
      Real.pi ^ (-3 / 4 : ℝ) *
        ‖Complex.Gamma ((3 / 4 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  · congr 1
    norm_num
  · congr 2
    push_cast
    ring

/-- One source-line real-Gamma quotient has exactly square-root conductor
growth.  The fourth-power form is arranged for the four Gamma factors in
the equation-(84) kernel. -/
theorem norm_GammaR_threeHalf_div_critical_pow_four_le (y : ℝ) :
    (‖Complex.Gammaℝ ((3 / 2 : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (y : ℂ) * I)‖) ^ 4 ≤
      Real.pi⁻¹ ^ 2 * Real.exp 8 * (1 + (y / 2) ^ 2) := by
  rw [norm_GammaR_threeHalf_sharp, norm_GammaR_critical_sharp]
  let A := ‖Complex.Gamma ((3 / 4 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖
  let B := ‖Complex.Gamma ((1 / 4 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖
  have hpi := Real.pi_pos
  have hB : 0 < B := by
    dsimp [B]
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpower :
      (Real.pi ^ (-3 / 4 : ℝ) / Real.pi ^ (-1 / 4 : ℝ)) ^ 4 =
        Real.pi⁻¹ ^ 2 := by
    rw [← Real.rpow_sub hpi]
    norm_num
    rw [← Real.rpow_mul_natCast hpi.le]
    norm_num
    rfl
  have halgebra :
      (Real.pi ^ (-3 / 4 : ℝ) * A /
          (Real.pi ^ (-1 / 4 : ℝ) * B)) ^ 4 =
        Real.pi⁻¹ ^ 2 * (A / B) ^ 4 := by
    rw [show Real.pi ^ (-3 / 4 : ℝ) * A /
        (Real.pi ^ (-1 / 4 : ℝ) * B) =
      (Real.pi ^ (-3 / 4 : ℝ) / Real.pi ^ (-1 / 4 : ℝ)) * (A / B) by
        field_simp [hB.ne', (Real.rpow_pos_of_pos hpi _).ne']]
    rw [mul_pow, hpower]
  change (Real.pi ^ (-3 / 4 : ℝ) * A /
      (Real.pi ^ (-1 / 4 : ℝ) * B)) ^ 4 ≤ _
  rw [halgebra]
  have hgamma := norm_Gamma_threeQuarter_div_quarter_pow_four_le (y / 2)
  change (A / B) ^ 4 ≤ _ at hgamma
  calc
    Real.pi⁻¹ ^ 2 * (A / B) ^ 4 ≤
        Real.pi⁻¹ ^ 2 * (Real.exp 8 * (1 + (y / 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left hgamma (by positivity)
    _ = Real.pi⁻¹ ^ 2 * Real.exp 8 * (1 + (y / 2) ^ 2) := by ring

/-- On the source line `Re w = 1`, the Hughes--Young Gamma quotient has an
explicit polynomial conductor cost.  This is the cancellation-preserving
source-line estimate needed to sum the equation-(84) shift tail; in
particular, it contains no unspecified `T ^ O(1)` exponent. -/
theorem norm_hughesYoungGammaRatioShift_one_le (t u : ℝ) :
    ‖hughesYoungGammaRatioShift t 1 u‖ ≤
      Real.exp (16 * u ^ 2) *
        (1 + Real.pi⁻¹ ^ 2 * Real.exp 8) ^ 2 *
        (1 + |t + u|) * (1 + |-t + u|) := by
  let Ap : ℝ :=
    ‖Complex.Gammaℝ ((3 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖
  let Am : ℝ :=
    ‖Complex.Gammaℝ ((3 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖
  let Cp : ℝ :=
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖
  let Cm : ℝ :=
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖
  let Bp : ℝ := ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖
  let Bm : ℝ :=
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖
  let rp : ℝ := Ap / Cp
  let rm : ℝ := Am / Cm
  let Kp : ℝ := Real.pi⁻¹ ^ 2 * Real.exp 8 *
    (1 + ((t + u) / 2) ^ 2)
  let Km : ℝ := Real.pi⁻¹ ^ 2 * Real.exp 8 *
    (1 + ((-t + u) / 2) ^ 2)
  let C₀ : ℝ := 1 + Real.pi⁻¹ ^ 2 * Real.exp 8
  have hCp : 0 < Cp := by
    dsimp only [Cp]
    exact norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hCm : 0 < Cm := by
    dsimp only [Cm]
    exact norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hBp : 0 < Bp := by
    dsimp only [Bp]
    exact norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hBm : 0 < Bm := by
    dsimp only [Bm]
    exact norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
  have hrp0 : 0 ≤ rp := by dsimp only [rp, Ap]; positivity
  have hrm0 : 0 ≤ rm := by dsimp only [rm, Am]; positivity
  have hKp0 : 0 ≤ Kp := by dsimp only [Kp]; positivity
  have hKm0 : 0 ≤ Km := by dsimp only [Km]; positivity
  have hC₀1 : 1 ≤ C₀ := by
    dsimp only [C₀]
    exact le_add_of_nonneg_right (by positivity)
  have hp : rp ^ 4 ≤ Kp := by
    simpa only [rp, Ap, Cp, Kp] using
      norm_GammaR_threeHalf_div_critical_pow_four_le (t + u)
  have hm : rm ^ 4 ≤ Km := by
    simpa only [rm, Am, Cm, Km] using
      norm_GammaR_threeHalf_div_critical_pow_four_le (-t + u)
  have hp2 : rp ^ 2 ≤ C₀ * (1 + |t + u|) := by
    apply (sq_le_sq₀ (sq_nonneg rp)
      (mul_nonneg (zero_le_one.trans hC₀1) (by positivity))).mp
    calc
      (rp ^ 2) ^ 2 = rp ^ 4 := by ring
      _ ≤ Kp := hp
      _ ≤ (C₀ * (1 + |t + u|)) ^ 2 := by
        dsimp only [Kp, C₀]
        have hdiv : ((t + u) / 2) ^ 2 = |t + u| ^ 2 / 4 := by
          rw [div_pow, ← sq_abs]
          norm_num
        rw [hdiv]
        let A : ℝ := Real.pi⁻¹ ^ 2 * Real.exp 8
        have hA : 0 ≤ A := by dsimp only [A]; positivity
        have hcoef : A ≤ (1 + A) ^ 2 := by
          nlinarith [sq_nonneg A]
        have hshape : 1 + |t + u| ^ 2 / 4 ≤ (1 + |t + u|) ^ 2 := by
          nlinarith [abs_nonneg (t + u), sq_nonneg |t + u|]
        change A * (1 + |t + u| ^ 2 / 4) ≤
          ((1 + A) * (1 + |t + u|)) ^ 2
        rw [mul_pow]
        exact mul_le_mul hcoef hshape (by positivity) (by positivity)
  have hm2 : rm ^ 2 ≤ C₀ * (1 + |-t + u|) := by
    apply (sq_le_sq₀ (sq_nonneg rm)
      (mul_nonneg (zero_le_one.trans hC₀1) (by positivity))).mp
    calc
      (rm ^ 2) ^ 2 = rm ^ 4 := by ring
      _ ≤ Km := hm
      _ ≤ (C₀ * (1 + |-t + u|)) ^ 2 := by
        dsimp only [Km, C₀]
        have hdiv : ((-t + u) / 2) ^ 2 = |-t + u| ^ 2 / 4 := by
          rw [div_pow, ← sq_abs]
          norm_num
        rw [hdiv]
        let A : ℝ := Real.pi⁻¹ ^ 2 * Real.exp 8
        have hA : 0 ≤ A := by dsimp only [A]; positivity
        have hcoef : A ≤ (1 + A) ^ 2 := by
          nlinarith [sq_nonneg A]
        have hshape : 1 + |-t + u| ^ 2 / 4 ≤ (1 + |-t + u|) ^ 2 := by
          nlinarith [abs_nonneg (-t + u), sq_nonneg |-t + u|]
        change A * (1 + |-t + u| ^ 2 / 4) ≤
          ((1 + A) * (1 + |-t + u|)) ^ 2
        rw [mul_pow]
        exact mul_le_mul hcoef hshape (by positivity) (by positivity)
  have hcritical := norm_GammaR_critical_symmetric_le t u
  change Cp * Cm ≤ Real.exp (8 * u ^ 2) * (Bp * Bm) at hcritical
  have hbase : 0 < Bp * Bm := mul_pos hBp hBm
  have hcriticalRatio : Cp * Cm / (Bp * Bm) ≤ Real.exp (8 * u ^ 2) := by
    exact (div_le_iff₀ hbase).2 (by simpa only [mul_assoc] using hcritical)
  have hcriticalRatio0 : 0 ≤ Cp * Cm / (Bp * Bm) := by positivity
  have hcriticalSq : (Cp * Cm / (Bp * Bm)) ^ 2 ≤ Real.exp (16 * u ^ 2) := by
    calc
      (Cp * Cm / (Bp * Bm)) ^ 2 ≤ (Real.exp (8 * u ^ 2)) ^ 2 := by
        exact (sq_le_sq₀ hcriticalRatio0 (Real.exp_pos _).le).2 hcriticalRatio
      _ = Real.exp (16 * u ^ 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hApCast :
      ‖Complex.Gammaℝ (((3 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ = Ap := by
    dsimp only [Ap]
    congr 2
    norm_num
  have hAmCast :
      ‖Complex.Gammaℝ (((3 / 2 : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ = Am := by
    dsimp only [Am]
    congr 2
    norm_num
  have hnorm : ‖hughesYoungGammaRatioShift t 1 u‖ =
      rp ^ 2 * rm ^ 2 * (Cp * Cm / (Bp * Bm)) ^ 2 := by
    rw [hughesYoungGammaRatioShift, afeGammaNormalization, norm_div,
      norm_mul, norm_pow, norm_pow, norm_mul, norm_pow, norm_pow]
    simp only [afeCriticalPoint]
    norm_num only [show (1 / 2 + 1 : ℝ) = 3 / 2 by norm_num]
    rw [hApCast, hAmCast]
    change Ap ^ 2 * Am ^ 2 / (Bp ^ 2 * Bm ^ 2) =
      rp ^ 2 * rm ^ 2 * (Cp * Cm / (Bp * Bm)) ^ 2
    dsimp only [rp, rm]
    field_simp [hCp.ne', hCm.ne', hBp.ne', hBm.ne']
  rw [hnorm]
  calc
    rp ^ 2 * rm ^ 2 * (Cp * Cm / (Bp * Bm)) ^ 2 ≤
        (C₀ * (1 + |t + u|)) * (C₀ * (1 + |-t + u|)) *
          Real.exp (16 * u ^ 2) := by gcongr
    _ = Real.exp (16 * u ^ 2) * C₀ ^ 2 *
        (1 + |t + u|) * (1 + |-t + u|) := by ring
    _ = Real.exp (16 * u ^ 2) *
        (1 + Real.pi⁻¹ ^ 2 * Real.exp 8) ^ 2 *
        (1 + |t + u|) * (1 + |-t + u|) := by rfl

/-- The completed-zeta pole normalization never creates conductor growth:
its reciprocal is bounded by the absolute constant `256`. -/
theorem norm_inv_afePoleNormalization_le (t : ℝ) :
    ‖(afePoleNormalization t)⁻¹‖ ≤ 256 := by
  have hfactor (v : ℝ) :
      (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ := by
    have h := Complex.abs_re_le_norm ((1 / 2 : ℂ) + (v : ℂ) * I)
    norm_num at h ⊢
    exact h
  have hfactorOne (v : ℝ) :
      (1 / 2 : ℝ) ≤ ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ := by
    have h := Complex.abs_re_le_norm (1 - ((1 / 2 : ℂ) + (v : ℂ) * I))
    norm_num at h ⊢
    exact h
  have hbase : (0 : ℝ) <
      ‖afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ := by
    rw [norm_pos_iff]
    repeat' apply mul_ne_zero
    · exact afeCriticalPoint_ne_zero t
    · exact sub_ne_zero.mpr (afeCriticalPoint_ne_one t).symm
    · exact afeCriticalPoint_ne_zero (-t)
    · exact sub_ne_zero.mpr (afeCriticalPoint_ne_one (-t)).symm
  have hprod : (1 / 16 : ℝ) ≤
      ‖afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ := by
    simp only [norm_mul]
    have h₁ := hfactor t
    have h₂ := hfactorOne t
    have h₃ := hfactor (-t)
    have h₄ := hfactorOne (-t)
    simp only [afeCriticalPoint] at h₁ h₂ h₃ h₄ ⊢
    calc
      (1 / 16 : ℝ) = (1 / 2) * (1 / 2) * (1 / 2) * (1 / 2) := by norm_num
      _ ≤ ‖1 / 2 + (t : ℂ) * I‖ * ‖1 - (1 / 2 + (t : ℂ) * I)‖ *
          ‖1 / 2 + ((-t : ℝ) : ℂ) * I‖ *
          ‖1 - (1 / 2 + ((-t : ℝ) : ℂ) * I)‖ := by gcongr
  rw [norm_inv, afePoleNormalization, norm_pow]
  have hsq : (1 / 256 : ℝ) ≤
      ‖afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ ^ 2 := by
    nlinarith [sq_nonneg
      (‖afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ - 1 / 16)]
  rw [inv_le_iff_one_le_mul₀' (pow_pos hbase 2)]
  nlinarith

/-- One real-Gamma quotient has the exact quarter-power conductor cost. -/
theorem norm_GammaR_one_div_critical_pow_four_le (y : ℝ) :
    (‖Complex.Gammaℝ ((1 : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (y : ℂ) * I)‖) ^ 4 ≤
      Real.pi⁻¹ * Real.exp 4 * Real.sqrt (1 + (y / 2) ^ 2) := by
  rw [norm_GammaR_one_sharp, norm_GammaR_critical_sharp]
  let A := ‖Complex.Gamma ((1 / 2 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖
  let B := ‖Complex.Gamma ((1 / 4 : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖
  have hpi := Real.pi_pos
  have hB : 0 < B := by
    dsimp [B]
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpower :
      (Real.pi ^ (-1 / 2 : ℝ) / Real.pi ^ (-1 / 4 : ℝ)) ^ 4 =
        Real.pi⁻¹ := by
    rw [← Real.rpow_sub hpi]
    norm_num
    rw [← Real.rpow_mul_natCast hpi.le]
    norm_num [Real.rpow_neg_one]
  have halgebra :
      (Real.pi ^ (-1 / 2 : ℝ) * A /
          (Real.pi ^ (-1 / 4 : ℝ) * B)) ^ 4 =
        Real.pi⁻¹ * (A / B) ^ 4 := by
    rw [show Real.pi ^ (-1 / 2 : ℝ) * A /
        (Real.pi ^ (-1 / 4 : ℝ) * B) =
      (Real.pi ^ (-1 / 2 : ℝ) / Real.pi ^ (-1 / 4 : ℝ)) * (A / B) by
        field_simp [hB.ne', (Real.rpow_pos_of_pos hpi _).ne']]
    rw [mul_pow, hpower]
  change (Real.pi ^ (-1 / 2 : ℝ) * A /
      (Real.pi ^ (-1 / 4 : ℝ) * B)) ^ 4 ≤ _
  rw [halgebra]
  have hgamma := norm_Gamma_half_div_quarter_pow_four_le (y / 2)
  change (A / B) ^ 4 ≤ _ at hgamma
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hgamma (inv_nonneg.mpr hpi.le)

/-- The moving residue has exactly one power of conductor growth. -/
theorem norm_hughesYoungGammaRatioShift_half_zero_le (t : ℝ) :
    ‖hughesYoungGammaRatioShift t (1 / 2) 0‖ ≤
      Real.exp 4 * (1 + |t|) := by
  let rp : ℝ :=
    ‖Complex.Gammaℝ ((1 : ℂ) + (t : ℂ) * I)‖ /
      ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖
  let rm : ℝ :=
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * I)‖ /
      ‖Complex.Gammaℝ ((1 / 2 : ℂ) - (t : ℂ) * I)‖
  let B : ℝ := Real.pi⁻¹ * Real.exp 4 * Real.sqrt (1 + (t / 2) ^ 2)
  have hrp : 0 ≤ rp := by dsimp [rp]; positivity
  have hrm : 0 ≤ rm := by dsimp [rm]; positivity
  have hp : rp ^ 4 ≤ B := by
    simpa only [rp, B] using norm_GammaR_one_div_critical_pow_four_le t
  have hm : rm ^ 4 ≤ B := by
    have hm0 := norm_GammaR_one_div_critical_pow_four_le (-t)
    simpa only [rm, B, neg_div, neg_sq, ofReal_neg, neg_mul,
      sub_eq_add_neg] using hm0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcombined : rp ^ 2 * rm ^ 2 ≤ B := by
    apply (sq_le_sq₀ (mul_nonneg (sq_nonneg rp) (sq_nonneg rm)) hB).mp
    calc
      (rp ^ 2 * rm ^ 2) ^ 2 = rp ^ 4 * rm ^ 4 := by ring
      _ ≤ B * B := mul_le_mul hp hm (pow_nonneg hrm 4) hB
      _ = B ^ 2 := by ring
  have hcriticalPlus :
      ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hcriticalMinus :
      ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hnorm : ‖hughesYoungGammaRatioShift t (1 / 2) 0‖ =
      rp ^ 2 * rm ^ 2 := by
    rw [hughesYoungGammaRatioShift, afeGammaNormalization, norm_div,
      norm_mul, norm_pow, norm_pow, norm_mul, norm_pow, norm_pow]
    simp only [afeCriticalPoint, add_zero]
    norm_num
    dsimp [rp, rm]
    field_simp [hcriticalPlus, hcriticalMinus]
    ring
  rw [hnorm]
  apply hcombined.trans
  have hpiInv : Real.pi⁻¹ ≤ 1 := by
    rw [inv_le_one₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  calc
    B = Real.pi⁻¹ *
        (Real.exp 4 * Real.sqrt (1 + (t / 2) ^ 2)) := by
          dsimp [B]
          ring
    _ ≤ 1 * (Real.exp 4 * Real.sqrt (1 + (t / 2) ^ 2)) :=
      mul_le_mul_of_nonneg_right hpiInv (by positivity)
    _ ≤ Real.exp 4 * (1 + |t|) := by
      have hsqrt : Real.sqrt (1 + (t / 2) ^ 2) ≤ 1 + |t| := by
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · have habsSq : |t| ^ 2 = t ^ 2 := sq_abs t
          nlinarith [abs_nonneg t, sq_nonneg t]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos 4).le

/-- The numerator Gamma pair at the moving residue retains its symmetric
vertical cancellation when the pole acquires a small imaginary part. -/
theorem norm_GammaR_one_symmetric_le (t u : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
        ‖Complex.Gammaℝ ((1 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ ≤
      Real.exp (8 * u ^ 2) *
        (‖Complex.Gammaℝ ((1 : ℂ) + (t : ℂ) * I)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * I)‖) := by
  rw [norm_GammaR_one_sharp, norm_GammaR_one_sharp,
    norm_GammaR_one_sharp]
  have hminus :
      ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * I)‖ =
        Real.pi ^ (-1 / 2 : ℝ) *
          ‖Complex.Gamma ((1 / 2 : ℂ) + ((-t / 2 : ℝ) : ℂ) * I)‖ := by
    have harg : (1 : ℂ) - (t : ℂ) * I =
        (1 : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg]
    exact norm_GammaR_one_sharp (-t)
  rw [hminus]
  have hgamma := norm_Gamma_symmetric_le_of_quarter_le
    (a := (1 / 2 : ℝ)) (by norm_num) (t / 2) (u / 2)
  have hnegShift :
      ‖Complex.Gamma ((1 / 2 : ℂ) + (((-t + u) / 2 : ℝ) : ℂ) * I)‖ =
        ‖Complex.Gamma ((1 / 2 : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I)‖ := by
    have h := norm_Gamma_vertical_neg_im (1 / 2) ((t - u) / 2)
    have hleft : (1 / 2 : ℂ) + (((-t + u) / 2 : ℝ) : ℂ) * I =
        (((1 / 2 : ℝ) : ℂ) + ((-((t - u) / 2) : ℝ) : ℂ) * I) := by
      push_cast
      ring
    have hright : (1 / 2 : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I =
        (((1 / 2 : ℝ) : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I) := by
      push_cast
      rfl
    rw [hleft, hright]
    exact h
  have hnegBase :
      ‖Complex.Gamma ((1 / 2 : ℂ) + ((-t / 2 : ℝ) : ℂ) * I)‖ =
        ‖Complex.Gamma ((1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
    have h := norm_Gamma_vertical_neg_im (1 / 2) (t / 2)
    have hleft : (1 / 2 : ℂ) + ((-t / 2 : ℝ) : ℂ) * I =
        (((1 / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I) := by
      push_cast
      ring
    have hright : (1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I =
        (((1 / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) := by
      push_cast
      rfl
    rw [hleft, hright]
    exact h
  rw [hnegShift, hnegBase]
  have hexp : Real.exp (32 * (u / 2) ^ 2) = Real.exp (8 * u ^ 2) := by
    congr 1
    ring
  rw [hexp] at hgamma
  have hgamma' :
      ‖Complex.Gamma ((1 / 2 : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I)‖ *
          ‖Complex.Gamma ((1 / 2 : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I)‖ ≤
        Real.exp (8 * u ^ 2) *
          ‖Complex.Gamma ((1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ^ 2 := by
    convert hgamma using 1 <;> congr 2 <;> push_cast <;> ring
  let p : ℝ := Real.pi ^ (-1 / 2 : ℝ)
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  calc
    p * ‖Complex.Gamma ((1 / 2 : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I)‖ *
          (p * ‖Complex.Gamma ((1 / 2 : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I)‖) =
        p ^ 2 *
          (‖Complex.Gamma ((1 / 2 : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I)‖ *
            ‖Complex.Gamma ((1 / 2 : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I)‖) := by ring
    _ ≤ p ^ 2 * (Real.exp (8 * u ^ 2) *
          ‖Complex.Gamma ((1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hgamma' (sq_nonneg p)
    _ = Real.exp (8 * u ^ 2) *
        (p * ‖Complex.Gamma ((1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ *
          (p * ‖Complex.Gamma ((1 / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖)) := by ring

/-- At the central real part, an arbitrary auxiliary imaginary displacement
costs only a Gaussian factor on top of the sharp one-conductor bound. -/
theorem norm_hughesYoungGammaRatioShift_half_le (t u : ℝ) :
    ‖hughesYoungGammaRatioShift t (1 / 2) u‖ ≤
      Real.exp (16 * u ^ 2 + 4) * (1 + |t|) := by
  let A : ℝ :=
    ‖Complex.Gammaℝ ((1 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
      ‖Complex.Gammaℝ ((1 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖
  let B : ℝ :=
    ‖Complex.Gammaℝ ((1 : ℂ) + (t : ℂ) * I)‖ *
      ‖Complex.Gammaℝ ((1 : ℂ) + ((-t : ℝ) : ℂ) * I)‖
  let D : ℝ := ‖afeGammaNormalization t‖
  have hD : 0 < D := by
    dsimp only [D]
    exact norm_pos_iff.mpr (afeGammaNormalization_ne_zero t)
  have hpair : A ≤ Real.exp (8 * u ^ 2) * B := by
    have hsource := norm_GammaR_one_symmetric_le t u
    have harg : (1 : ℂ) - (t : ℂ) * I =
        (1 : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg] at hsource
    simpa only [A, B] using hsource
  have hcenter := norm_hughesYoungGammaRatioShift_half_zero_le t
  have hcenterEq : ‖hughesYoungGammaRatioShift t (1 / 2) 0‖ = B ^ 2 / D := by
    rw [hughesYoungGammaRatioShift, norm_div, norm_mul, norm_pow, norm_pow]
    simp only [add_zero]
    dsimp only [B, D]
    norm_num
    ring
  have hnorm : ‖hughesYoungGammaRatioShift t (1 / 2) u‖ = A ^ 2 / D := by
    rw [hughesYoungGammaRatioShift, norm_div, norm_mul, norm_pow, norm_pow]
    dsimp only [A, D]
    norm_num
    ring
  rw [hcenterEq] at hcenter
  rw [hnorm]
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  calc
    A ^ 2 / D ≤ (Real.exp (8 * u ^ 2) * B) ^ 2 / D := by gcongr
    _ = Real.exp (16 * u ^ 2) * (B ^ 2 / D) := by
      rw [show Real.exp (16 * u ^ 2) = Real.exp (8 * u ^ 2) ^ 2 by
        rw [← Real.exp_nat_mul]
        congr 1
        ring]
      ring
    _ ≤ Real.exp (16 * u ^ 2) * (Real.exp 4 * (1 + |t|)) := by
      gcongr
    _ = Real.exp (16 * u ^ 2 + 4) * (1 + |t|) := by
      rw [Real.exp_add]
      ring

/-! ## Stability of the sharp ratio in a small horizontal neighbourhood -/

/-- Moving an ordinary Gamma factor a signed distance at most `1/8` from
`Re z = 1/2` costs only the expected exponential of distance times the
logarithmic height.  The signed formulation is needed at the moving
Hughes--Young pole, where the two auxiliary shifts can move the pole to
either side of `Re W = 1/2`. -/
theorem exists_norm_Gamma_half_horizontal_displacement_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (d : ℝ),
      z.re = 1 / 2 → |d| ≤ 1 / 8 →
      ‖Complex.Gamma (z + (d : ℂ))‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp (C * |d| * Real.log (|z.im| + 2)) := by
  obtain ⟨C, hC, hdigamma⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (3 / 8 : ℝ)) (b := (5 / 8 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro z d hzre hd
  by_cases hd0 : 0 ≤ d
  · let f : ℝ → ℂ := fun x => Complex.Gamma (z + (x : ℂ))
    let f' : ℝ → ℂ := fun x =>
      Complex.Gamma (z + (x : ℂ)) * Complex.digamma (z + (x : ℂ))
    let K : ℝ := C * Real.log (|z.im| + 2)
    have hlog : 0 ≤ Real.log (|z.im| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg z.im])
    have hK : 0 ≤ K := mul_nonneg hC.le hlog
    have hdUpper : d ≤ 1 / 8 := by simpa [abs_of_nonneg hd0] using hd
    have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
        0 < (z + (x : ℂ)).re := by
      simp only [add_re, ofReal_re, hzre]
      linarith [hx.1]
    have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
        HasDerivAt f (f' x) x := by
      have houter := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos (hzpos x hx)
      have hshift : HasDerivAt (fun w : ℂ => z + w) 1 (x : ℂ) :=
        (hasDerivAt_id (x : ℂ)).const_add z
      convert (houter.comp (x : ℂ) hshift).comp_ofReal using 1
      all_goals simp only [f']
      all_goals ring
    have hfcont : ContinuousOn f (Set.Icc 0 d) := by
      intro x hx
      exact (hfderiv x hx).continuousAt.continuousWithinAt
    have hderivWithin : ∀ x ∈ Set.Ico 0 d,
        HasDerivWithinAt f (f' x) (Set.Ici x) x := by
      intro x hx
      exact (hfderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico 0 d,
        ‖f' x‖ ≤ K * ‖f x‖ + 0 := by
      intro x hx
      have hxLower : (3 / 8 : ℝ) ≤ (z + (x : ℂ)).re := by
        simp only [add_re, ofReal_re, hzre]
        linarith [hx.1]
      have hxUpper : (z + (x : ℂ)).re ≤ (5 / 8 : ℝ) := by
        simp only [add_re, ofReal_re, hzre]
        linarith [hx.2.le, hdUpper]
      have him : (z + (x : ℂ)).im = z.im := by simp
      have hpsi := hdigamma (z + (x : ℂ)) hxLower hxUpper
      rw [him] at hpsi
      simp only [f', f, norm_mul, add_zero]
      calc
        ‖Complex.Gamma (z + (x : ℂ))‖ *
              ‖Complex.digamma (z + (x : ℂ))‖ ≤
            ‖Complex.Gamma (z + (x : ℂ))‖ *
              (C * Real.log (|z.im| + 2)) :=
          mul_le_mul_of_nonneg_left hpsi (norm_nonneg _)
        _ = K * ‖Complex.Gamma (z + (x : ℂ))‖ := by
          dsimp only [K]
          ring
    have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
      hfcont hderivWithin (show ‖f 0‖ ≤ ‖f 0‖ by rfl) hbound d
      (show d ∈ Set.Icc 0 d from ⟨hd0, le_rfl⟩)
    rw [gronwallBound_ε0, sub_zero] at hgronwall
    change ‖Complex.Gamma (z + (d : ℂ))‖ ≤
      ‖Complex.Gamma z‖ *
        Real.exp (C * |d| * Real.log (|z.im| + 2))
    rw [abs_of_nonneg hd0]
    convert hgronwall using 1
    all_goals simp only [f, ofReal_zero, add_zero, K]
    all_goals ring
  · have hdneg : d < 0 := lt_of_not_ge hd0
    let e : ℝ := -d
    let f : ℝ → ℂ := fun x => Complex.Gamma (z - (x : ℂ))
    let f' : ℝ → ℂ := fun x =>
      -(Complex.Gamma (z - (x : ℂ)) * Complex.digamma (z - (x : ℂ)))
    let K : ℝ := C * Real.log (|z.im| + 2)
    have he0 : 0 ≤ e := by dsimp only [e]; linarith
    have heUpper : e ≤ 1 / 8 := by
      simpa [e, abs_of_neg hdneg] using hd
    have hlog : 0 ≤ Real.log (|z.im| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg z.im])
    have hK : 0 ≤ K := mul_nonneg hC.le hlog
    have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 e) :
        0 < (z - (x : ℂ)).re := by
      simp only [sub_re, ofReal_re, hzre]
      linarith [hx.2, heUpper]
    have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 e) :
        HasDerivAt f (f' x) x := by
      have houter := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos (hzpos x hx)
      have hshift : HasDerivAt (fun w : ℂ => z - w) (-1) (x : ℂ) :=
        by simpa using
          (hasDerivAt_const (x := (x : ℂ)) z).sub (hasDerivAt_id (x : ℂ))
      convert (houter.comp (x : ℂ) hshift).comp_ofReal using 1
      all_goals simp only [f']
      all_goals ring
    have hfcont : ContinuousOn f (Set.Icc 0 e) := by
      intro x hx
      exact (hfderiv x hx).continuousAt.continuousWithinAt
    have hderivWithin : ∀ x ∈ Set.Ico 0 e,
        HasDerivWithinAt f (f' x) (Set.Ici x) x := by
      intro x hx
      exact (hfderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico 0 e,
        ‖f' x‖ ≤ K * ‖f x‖ + 0 := by
      intro x hx
      have hxLower : (3 / 8 : ℝ) ≤ (z - (x : ℂ)).re := by
        simp only [sub_re, ofReal_re, hzre]
        linarith [hx.2.le, heUpper]
      have hxUpper : (z - (x : ℂ)).re ≤ (5 / 8 : ℝ) := by
        simp only [sub_re, ofReal_re, hzre]
        linarith [hx.1]
      have him : (z - (x : ℂ)).im = z.im := by simp
      have hpsi := hdigamma (z - (x : ℂ)) hxLower hxUpper
      rw [him] at hpsi
      simp only [f', f, norm_neg, norm_mul, add_zero]
      calc
        ‖Complex.Gamma (z - (x : ℂ))‖ *
              ‖Complex.digamma (z - (x : ℂ))‖ ≤
            ‖Complex.Gamma (z - (x : ℂ))‖ *
              (C * Real.log (|z.im| + 2)) :=
          mul_le_mul_of_nonneg_left hpsi (norm_nonneg _)
        _ = K * ‖Complex.Gamma (z - (x : ℂ))‖ := by
          dsimp only [K]
          ring
    have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
      hfcont hderivWithin (show ‖f 0‖ ≤ ‖f 0‖ by rfl) hbound e
      (show e ∈ Set.Icc 0 e from ⟨he0, le_rfl⟩)
    rw [gronwallBound_ε0, sub_zero] at hgronwall
    change ‖Complex.Gamma (z + (d : ℂ))‖ ≤
      ‖Complex.Gamma z‖ *
        Real.exp (C * |d| * Real.log (|z.im| + 2))
    have hde : (d : ℂ) = -(e : ℂ) := by simp [e]
    rw [hde, ← sub_eq_add_neg, abs_of_neg hdneg]
    convert hgronwall using 1
    all_goals simp only [f, ofReal_zero, sub_zero, K, e]
    all_goals ring

/-- The corresponding signed neighbourhood estimate for Deligne's real
Gamma factor.  The harmless factor `4` bounds the variation of the real
power of `π`; all height dependence remains proportional to the actual
distance from the residue line. -/
theorem exists_norm_GammaR_one_horizontal_displacement_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (y c : ℝ), |c - 1 / 2| ≤ 1 / 4 →
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        4 * ‖Complex.Gammaℝ ((1 : ℂ) + (y : ℂ) * I)‖ *
          Real.exp (C * |c - 1 / 2| * Real.log (|y| + 2)) := by
  obtain ⟨C, hC, hGamma⟩ :=
    exists_norm_Gamma_half_horizontal_displacement_le
  refine ⟨C, hC, ?_⟩
  intro y c hc
  let z : ℂ := (1 / 2 : ℂ) + ((y / 2 : ℝ) : ℂ) * I
  let d : ℝ := (c - 1 / 2) / 2
  let pShift : ℝ := Real.pi ^ (-(1 / 2 + c) / 2)
  let pBase : ℝ := Real.pi ^ (-1 / 2 : ℝ)
  have hzre : z.re = 1 / 2 := by simp [z]
  have hd : |d| ≤ 1 / 8 := by
    dsimp only [d]
    rw [abs_div]
    norm_num
    linarith
  have hGamma' := hGamma z d hzre hd
  have hlogArg : |z.im| + 2 ≤ |y| + 2 := by
    have hzim : z.im = y / 2 := by simp [z]
    rw [hzim]
    rw [abs_div]
    norm_num
  have hlogSmall : 0 ≤ Real.log (|z.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hlogLarge : 0 ≤ Real.log (|y| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg y])
  have hlog : Real.log (|z.im| + 2) ≤ Real.log (|y| + 2) :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) hlogArg
  have hdAbs : |d| = |c - 1 / 2| / 2 := by
    dsimp only [d]
    rw [abs_div]
    norm_num
  have hexponent : C * |d| * Real.log (|z.im| + 2) ≤
      C * |c - 1 / 2| * Real.log (|y| + 2) := by
    rw [hdAbs]
    calc
      C * (|c - 1 / 2| / 2) * Real.log (|z.im| + 2) ≤
          C * (|c - 1 / 2| / 2) * Real.log (|y| + 2) := by gcongr
      _ ≤ C * |c - 1 / 2| * Real.log (|y| + 2) := by
        have hhalf : |c - 1 / 2| / 2 ≤ |c - 1 / 2| := by
          linarith [abs_nonneg (c - 1 / 2)]
        calc
          C * (|c - 1 / 2| / 2) * Real.log (|y| + 2) =
              (C * Real.log (|y| + 2)) * (|c - 1 / 2| / 2) := by ring
          _ ≤ (C * Real.log (|y| + 2)) * |c - 1 / 2| :=
            mul_le_mul_of_nonneg_left hhalf (mul_nonneg hC.le hlogLarge)
          _ = C * |c - 1 / 2| * Real.log (|y| + 2) := by ring
  have hGammaLarge : ‖Complex.Gamma (z + (d : ℂ))‖ ≤
      ‖Complex.Gamma z‖ *
        Real.exp (C * |c - 1 / 2| * Real.log (|y| + 2)) :=
    hGamma'.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hexponent) (norm_nonneg _))
  have hpiOne : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hminusD : -d ≤ 1 := by
    have hdle := le_trans hd (by norm_num : (1 / 8 : ℝ) ≤ 1)
    exact (le_abs_self (-d)).trans (by simpa only [abs_neg] using hdle)
  have hpiPow : Real.pi ^ (-d) ≤ 4 := by
    calc
      Real.pi ^ (-d) ≤ Real.pi ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpiOne hminusD
      _ = Real.pi := Real.rpow_one _
      _ ≤ 4 := Real.pi_lt_four.le
  have hpShift : pShift = pBase * Real.pi ^ (-d) := by
    dsimp only [pShift, pBase, d]
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hpBase0 : 0 ≤ pBase := by dsimp only [pBase]; positivity
  have hpLe : pShift ≤ 4 * pBase := by
    rw [hpShift]
    nlinarith [mul_le_mul_of_nonneg_left hpiPow hpBase0]
  have hShiftNorm :
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        pShift * ‖Complex.Gamma (z + (d : ℂ))‖ := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · dsimp only [pShift]
      congr 1
      simp
    · congr 2
      dsimp only [z, d]
      push_cast
      ring
  have hBaseNorm :
      ‖Complex.Gammaℝ ((1 : ℂ) + (y : ℂ) * I)‖ =
        pBase * ‖Complex.Gamma z‖ := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · dsimp only [pBase]
      congr 1
      norm_num
    · congr 2
      dsimp only [z]
      push_cast
      ring
  rw [hShiftNorm, hBaseNorm]
  calc
    pShift * ‖Complex.Gamma (z + (d : ℂ))‖ ≤
        (4 * pBase) *
          (‖Complex.Gamma z‖ *
            Real.exp (C * |c - 1 / 2| * Real.log (|y| + 2))) := by
      exact mul_le_mul hpLe hGammaLarge (norm_nonneg _)
        (le_trans (Real.rpow_nonneg (le_of_lt Real.pi_pos) _) hpLe)
    _ = 4 * (pBase * ‖Complex.Gamma z‖) *
          Real.exp (C * |c - 1 / 2| * Real.log (|y| + 2)) := by ring

/-- Uniform sharp conductor bound for the Hughes--Young Gamma ratio in a
small horizontal neighbourhood of its moving-residue line.  The baseline
at `c = 1/2` is the exact one-conductor estimate; moving a distance `d`
costs only `exp (O(d log(height)))`. -/
theorem exists_norm_hughesYoungGammaRatioShift_near_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u c : ℝ), |c - 1 / 2| ≤ 1 / 4 →
      ‖hughesYoungGammaRatioShift t c u‖ ≤
        256 * Real.exp
          (16 * u ^ 2 + 4 +
            4 * C * |c - 1 / 2| * Real.log (|t| + |u| + 2)) *
          (1 + |t|) := by
  obtain ⟨C, hC, hshift⟩ :=
    exists_norm_GammaR_one_horizontal_displacement_le
  refine ⟨C, hC, ?_⟩
  intro t u c hc
  let Aplus : ℝ :=
    ‖Complex.Gammaℝ
      (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)‖
  let Aminus : ℝ :=
    ‖Complex.Gammaℝ
      (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖
  let Bplus : ℝ :=
    ‖Complex.Gammaℝ ((1 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖
  let Bminus : ℝ :=
    ‖Complex.Gammaℝ ((1 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖
  let D : ℝ := ‖afeGammaNormalization t‖
  let L : ℝ := Real.log (|t| + |u| + 2)
  let d : ℝ := |c - 1 / 2|
  have hD : 0 < D := by
    dsimp only [D]
    exact norm_pos_iff.mpr (afeGammaNormalization_ne_zero t)
  have hbase : 0 ≤ |t| + |u| + 2 := by positivity
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg (by linarith [abs_nonneg t, abs_nonneg u])
  have hplusArg : |t + u| + 2 ≤ |t| + |u| + 2 := by
    linarith [abs_add_le t u]
  have hminusArg : |-t + u| + 2 ≤ |t| + |u| + 2 := by
    have htri := abs_add_le (-t) u
    rw [abs_neg] at htri
    linarith
  have hplusLog : Real.log (|t + u| + 2) ≤ L := by
    dsimp only [L]
    exact Real.log_le_log (by linarith [abs_nonneg (t + u)]) hplusArg
  have hminusLog : Real.log (|-t + u| + 2) ≤ L := by
    dsimp only [L]
    exact Real.log_le_log (by linarith [abs_nonneg (-t + u)]) hminusArg
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hplusRaw := hshift (t + u) c hc
  have hminusRaw := hshift (-t + u) c hc
  have hplus : Aplus ≤ 4 * Bplus * Real.exp (C * d * L) := by
    dsimp only [Aplus, Bplus, d] at hplusRaw ⊢
    exact hplusRaw.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hplusLog
        (mul_nonneg hC.le (abs_nonneg (c - 1 / 2)))))
      (mul_nonneg (by norm_num) (norm_nonneg _)))
  have hminus : Aminus ≤ 4 * Bminus * Real.exp (C * d * L) := by
    dsimp only [Aminus, Bminus, d] at hminusRaw ⊢
    exact hminusRaw.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hminusLog
        (mul_nonneg hC.le (abs_nonneg (c - 1 / 2)))))
      (mul_nonneg (by norm_num) (norm_nonneg _)))
  have hpair : Aplus * Aminus ≤
      16 * (Bplus * Bminus) * Real.exp (2 * C * d * L) := by
    have hAp0 : 0 ≤ Aplus := by dsimp only [Aplus]; positivity
    have hAm0 : 0 ≤ Aminus := by dsimp only [Aminus]; positivity
    have hBp0 : 0 ≤ Bplus := by dsimp only [Bplus]; positivity
    have hBm0 : 0 ≤ Bminus := by dsimp only [Bminus]; positivity
    calc
      Aplus * Aminus ≤
          (4 * Bplus * Real.exp (C * d * L)) *
            (4 * Bminus * Real.exp (C * d * L)) :=
        mul_le_mul hplus hminus hAm0
          (mul_nonneg (mul_nonneg (by norm_num) hBp0) (Real.exp_nonneg _))
      _ = 16 * (Bplus * Bminus) * Real.exp (2 * C * d * L) := by
        rw [show Real.exp (2 * C * d * L) =
            Real.exp (C * d * L) ^ 2 by
          rw [← Real.exp_nat_mul]
          congr 1
          ring]
        ring
  have hcenter := norm_hughesYoungGammaRatioShift_half_le t u
  have hcenterEq :
      ‖hughesYoungGammaRatioShift t (1 / 2) u‖ =
        (Bplus * Bminus) ^ 2 / D := by
    rw [hughesYoungGammaRatioShift, norm_div, norm_mul, norm_pow, norm_pow]
    simp only [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num]
    change Bplus ^ 2 * Bminus ^ 2 / D = (Bplus * Bminus) ^ 2 / D
    ring
  have hnorm : ‖hughesYoungGammaRatioShift t c u‖ =
      (Aplus * Aminus) ^ 2 / D := by
    rw [hughesYoungGammaRatioShift, norm_div, norm_mul, norm_pow, norm_pow]
    dsimp only [Aplus, Aminus, D]
    ring
  rw [hcenterEq] at hcenter
  rw [hnorm]
  have hpair0 : 0 ≤ Bplus * Bminus := by
    dsimp only [Bplus, Bminus]
    positivity
  calc
    (Aplus * Aminus) ^ 2 / D ≤
        (16 * (Bplus * Bminus) * Real.exp (2 * C * d * L)) ^ 2 / D := by
      gcongr
    _ = 256 * Real.exp (4 * C * d * L) *
          ((Bplus * Bminus) ^ 2 / D) := by
      rw [show Real.exp (4 * C * d * L) =
          Real.exp (2 * C * d * L) ^ 2 by
        rw [← Real.exp_nat_mul]
        congr 1
        ring]
      ring
    _ ≤ 256 * Real.exp (4 * C * d * L) *
          (Real.exp (16 * u ^ 2 + 4) * (1 + |t|)) := by
      gcongr
    _ = 256 *
          (Real.exp (4 * C * d * L) * Real.exp (16 * u ^ 2 + 4)) *
          (1 + |t|) := by ring
    _ = 256 * Real.exp
          (4 * C * d * L + (16 * u ^ 2 + 4)) * (1 + |t|) := by
      rw [← Real.exp_add]
    _ = 256 * Real.exp
          (16 * u ^ 2 + 4 + 4 * C * d * L) * (1 + |t|) := by
      congr 3
      ring

end RiemannZeta.GuthMaynard
