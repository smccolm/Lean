import Mathlib.Analysis.Convex.Deriv
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

open Complex Set Filter

noncomputable section

namespace RiemannZeta.GuthMaynard

private noncomputable def logQuadSemiconvex (A y : ℝ) : ℝ :=
  Real.log (A ^ 2 + y ^ 2) + y ^ 2 / A ^ 2

private theorem convex_logQuadSemiconvex {A : ℝ} (hA : 0 < A) :
    ConvexOn ℝ Set.univ (logQuadSemiconvex A) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (by
      unfold logQuadSemiconvex
      have hpoly : Continuous (fun y : ℝ => A ^ 2 + y ^ 2) := by fun_prop
      have hlog : Continuous (fun y : ℝ => Real.log (A ^ 2 + y ^ 2)) := by
        rw [continuous_iff_continuousAt]
        intro y
        exact hpoly.continuousAt.log (by positivity)
      exact (hlog.add (by fun_prop)).continuousOn)
    (f' := fun y => 2 * y / (A ^ 2 + y ^ 2) + 2 * y / A ^ 2)
    (f'' := fun y => 2 * (A ^ 2 - y ^ 2) / (A ^ 2 + y ^ 2) ^ 2 + 2 / A ^ 2)
  · intro y _
    have hden : A ^ 2 + y ^ 2 ≠ 0 := by positivity
    have hinner : HasDerivAt (fun x : ℝ => A ^ 2 + x ^ 2) (2 * y) y := by
      convert (hasDerivAt_const y (A ^ 2)).add (hasDerivAt_pow 2 y) using 1
      all_goals ring_nf
    have hlog := (Real.hasDerivAt_log hden).comp y hinner
    have hsq := (hasDerivAt_pow 2 y).div_const (A ^ 2)
    apply HasDerivAt.hasDerivWithinAt
    convert hlog.add hsq using 1
    all_goals field_simp
    all_goals ring_nf
  · intro y _
    have hden : A ^ 2 + y ^ 2 ≠ 0 := by positivity
    have hinner : HasDerivAt (fun x : ℝ => A ^ 2 + x ^ 2) (2 * y) y := by
      convert (hasDerivAt_const y (A ^ 2)).add (hasDerivAt_pow 2 y) using 1
      all_goals ring_nf
    have hnum : HasDerivAt (fun x : ℝ => 2 * x) 2 y := by
      convert (hasDerivAt_id y).const_mul 2 using 1
      all_goals ring_nf
    have hquot := hnum.div hinner hden
    have hlin := ((hasDerivAt_id y).const_mul 2).div_const (A ^ 2)
    apply HasDerivAt.hasDerivWithinAt
    convert hquot.add hlin using 1
    all_goals field_simp
    all_goals ring_nf
  · intro y _
    have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
    have hden : 0 < A ^ 2 + y ^ 2 := by positivity
    have hden2 : 0 < (A ^ 2 + y ^ 2) ^ 2 := sq_pos_of_pos hden
    rw [show
      2 * (A ^ 2 - y ^ 2) / (A ^ 2 + y ^ 2) ^ 2 + 2 / A ^ 2 =
        2 * (2 * A ^ 4 + A ^ 2 * y ^ 2 + y ^ 4) /
          ((A ^ 2 + y ^ 2) ^ 2 * A ^ 2) by
      field_simp [hA2.ne', hden2.ne']
      ring]
    positivity

/-- The logarithmic quadratic denominator occurring in the Weierstrass
product for `Gamma` is uniformly semiconvex.  This symmetric form is what
preserves the cancellation between the ordinates `t+u` and `t-u`. -/
theorem logQuad_symmetric_difference_le {A : ℝ} (hA : 0 < A) (t u : ℝ) :
    2 * Real.log (A ^ 2 + t ^ 2) -
        Real.log (A ^ 2 + (t + u) ^ 2) -
        Real.log (A ^ 2 + (t - u) ^ 2) ≤
      2 * u ^ 2 / A ^ 2 := by
  have hconv := convex_logQuadSemiconvex hA
  have hmid := hconv.2 (Set.mem_univ (t + u)) (Set.mem_univ (t - u))
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid' :
      logQuadSemiconvex A t ≤
        (1 / 2 : ℝ) * logQuadSemiconvex A (t + u) +
          (1 / 2 : ℝ) * logQuadSemiconvex A (t - u) := by
    convert hmid using 1
    all_goals norm_num [smul_eq_mul]
    all_goals ring_nf
  unfold logQuadSemiconvex at hmid'
  ring_nf at hmid' ⊢
  nlinarith

private theorem norm_real_add_mul_I (a y : ℝ) :
    ‖(a : ℂ) + (y : ℂ) * I‖ = Real.sqrt (a ^ 2 + y ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq, sq]

/-- Exact norm of Euler's finite Gamma product on a right-half-plane
vertical line. -/
theorem norm_GammaSeq_vertical {a y : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((a : ℂ) + (y : ℂ) * I) n‖ =
      (n : ℝ) ^ a * (n.factorial : ℝ) /
        ∏ j ∈ Finset.range (n + 1), Real.sqrt ((a + j) ^ 2 + y ^ 2) := by
  unfold Complex.GammaSeq
  rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero,
    zero_mul, sub_zero, add_zero, norm_natCast, norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  convert norm_real_add_mul_I (a + j) y using 1
  all_goals push_cast
  all_goals ring_nf

private noncomputable def gammaDenom (a y : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (n + 1), Real.sqrt ((a + j) ^ 2 + y ^ 2)

private theorem gammaDenom_pos {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
    0 < gammaDenom a y n := by
  unfold gammaDenom
  apply Finset.prod_pos
  intro j _
  apply Real.sqrt_pos.2
  have : 0 < a + j := by positivity
  positivity

private theorem log_gammaDenom {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
    Real.log (gammaDenom a y n) =
      (1 / 2 : ℝ) *
        ∑ j ∈ Finset.range (n + 1), Real.log ((a + j) ^ 2 + y ^ 2) := by
  unfold gammaDenom
  rw [Real.log_prod]
  · calc
      ∑ j ∈ Finset.range (n + 1), Real.log (Real.sqrt ((a + j) ^ 2 + y ^ 2)) =
          ∑ j ∈ Finset.range (n + 1), Real.log ((a + j) ^ 2 + y ^ 2) / 2 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Real.log_sqrt (by positivity)]
      _ = (1 / 2 : ℝ) *
          ∑ j ∈ Finset.range (n + 1), Real.log ((a + j) ^ 2 + y ^ 2) := by
            simp only [div_eq_mul_inv, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
  · intro j hj
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have : 0 < a + j := by positivity
    positivity

private theorem reciprocal_quarter_sum_le (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), 1 / ((1 / 4 : ℝ) + j) ^ 2 ≤ 32 := by
  have hpoint : ∀ j : ℕ,
      1 / ((1 / 4 : ℝ) + j) ^ 2 ≤ 16 * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hleft : 0 < (1 / 4 : ℝ) + j := by positivity
    have hright : 0 < (j : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (sq_pos_of_pos hleft), div_eq_mul_inv]
    field_simp [hleft.ne', hright.ne']
    nlinarith [sq_nonneg ((j : ℝ) + 1)]
  calc
    ∑ j ∈ Finset.range (n + 1), 1 / ((1 / 4 : ℝ) + j) ^ 2
        ≤ ∑ j ∈ Finset.range (n + 1), 16 * (1 / ((j : ℝ) + 1) ^ 2) :=
          Finset.sum_le_sum fun j _ => hpoint j
    _ ≤ 16 * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left
        (Complex.summable_one_div_natCast_add_one_sq.sum_le_tsum
          (Finset.range (n + 1)) (fun j _ => by positivity))
        (by norm_num)
    _ ≤ 32 := by
      have hs := Complex.summable_one_div_natCast_add_one_sq
      rw [hs.tsum_eq_zero_add]
      have htail := Complex.tsum_one_div_natCast_add_add_one_sq_le
        (N := 1) (by norm_num)
      norm_num at htail ⊢
      linarith

/-- The exact finite Euler products already exhibit the cancellation in the
two opposite critical-line Gamma factors. -/
theorem gammaDenom_symmetric_ratio_le (t u : ℝ) (n : ℕ) :
    gammaDenom (1 / 4) t n ^ 2 /
        (gammaDenom (1 / 4) (t + u) n * gammaDenom (1 / 4) (t - u) n) ≤
      Real.exp (32 * u ^ 2) := by
  have hsum :
      2 * Real.log (gammaDenom (1 / 4) t n) -
          Real.log (gammaDenom (1 / 4) (t + u) n) -
          Real.log (gammaDenom (1 / 4) (t - u) n) ≤
        32 * u ^ 2 := by
    rw [log_gammaDenom (by norm_num), log_gammaDenom (by norm_num),
      log_gammaDenom (by norm_num)]
    have hterm : ∀ j ∈ Finset.range (n + 1),
        2 * Real.log (((1 / 4 : ℝ) + j) ^ 2 + t ^ 2) -
            Real.log (((1 / 4 : ℝ) + j) ^ 2 + (t + u) ^ 2) -
            Real.log (((1 / 4 : ℝ) + j) ^ 2 + (t - u) ^ 2) ≤
          2 * u ^ 2 / ((1 / 4 : ℝ) + j) ^ 2 := by
      intro j _
      exact logQuad_symmetric_difference_le (by positivity) t u
    have hs := Finset.sum_le_sum hterm
    simp_rw [Finset.sum_sub_distrib] at hs
    rw [← Finset.mul_sum] at hs
    have hrhs :
        ∑ j ∈ Finset.range (n + 1),
            2 * u ^ 2 / ((1 / 4 : ℝ) + j) ^ 2 =
          2 * u ^ 2 *
            ∑ j ∈ Finset.range (n + 1), 1 / ((1 / 4 : ℝ) + j) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hrec := reciprocal_quarter_sum_le n
    rw [hrhs] at hs
    nlinarith [mul_le_mul_of_nonneg_left hrec (sq_nonneg u)]
  have hpos0 := gammaDenom_pos (by norm_num : (0 : ℝ) < 1 / 4) t n
  have hposp := gammaDenom_pos (by norm_num : (0 : ℝ) < 1 / 4) (t + u) n
  have hposm := gammaDenom_pos (by norm_num : (0 : ℝ) < 1 / 4) (t - u) n
  rw [← Real.exp_log (div_pos (sq_pos_of_pos hpos0) (mul_pos hposp hposm))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (pow_ne_zero 2 hpos0.ne') (mul_ne_zero hposp.ne' hposm.ne'),
    Real.log_pow, Real.log_mul hposp.ne' hposm.ne']
  linarith

/-- The symmetric Gamma-pair estimate at the finite Euler-product level. -/
theorem norm_GammaSeq_symmetric_le (t u : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((1 / 4 : ℂ) + ((t + u : ℝ) : ℂ) * I) n‖ *
        ‖Complex.GammaSeq ((1 / 4 : ℂ) + ((t - u : ℝ) : ℂ) * I) n‖ ≤
      Real.exp (32 * u ^ 2) *
        ‖Complex.GammaSeq ((1 / 4 : ℂ) + (t : ℂ) * I) n‖ ^ 2 := by
  have hquarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hquarter]
  rw [norm_GammaSeq_vertical hn, norm_GammaSeq_vertical hn,
    norm_GammaSeq_vertical hn]
  let C : ℝ := (n : ℝ) ^ (1 / 4 : ℝ) * (n.factorial : ℝ)
  let D0 := gammaDenom (1 / 4) t n
  let Dp := gammaDenom (1 / 4) (t + u) n
  let Dm := gammaDenom (1 / 4) (t - u) n
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hD0 : 0 < D0 := gammaDenom_pos (by norm_num) t n
  have hDp : 0 < Dp := gammaDenom_pos (by norm_num) (t + u) n
  have hDm : 0 < Dm := gammaDenom_pos (by norm_num) (t - u) n
  have hratio : D0 ^ 2 / (Dp * Dm) ≤ Real.exp (32 * u ^ 2) := by
    simpa only [D0, Dp, Dm] using gammaDenom_symmetric_ratio_le t u n
  have hfactor : 0 ≤ C ^ 2 / D0 ^ 2 := by positivity
  calc
    C / Dp * (C / Dm) =
        (C ^ 2 / D0 ^ 2) * (D0 ^ 2 / (Dp * Dm)) := by
          field_simp [hD0.ne', hDp.ne', hDm.ne']
    _ ≤ (C ^ 2 / D0 ^ 2) * Real.exp (32 * u ^ 2) :=
      mul_le_mul_of_nonneg_left hratio hfactor
    _ = Real.exp (32 * u ^ 2) * (C / D0) ^ 2 := by ring

/-- Uniform symmetric growth of Gamma on the vertical line `Re z = 1/4`.
Unlike a one-sided Stirling bound, this retains the cancellation between the
two shifts and is uniform in the central ordinate. -/
theorem norm_Gamma_symmetric_le (t u : ℝ) :
    ‖Complex.Gamma ((1 / 4 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
        ‖Complex.Gamma ((1 / 4 : ℂ) + ((t - u : ℝ) : ℂ) * I)‖ ≤
      Real.exp (32 * u ^ 2) *
        ‖Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hquarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hquarter]
  let zp : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
  let zm : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I
  let z0 : ℂ := ((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hp : Tendsto (fun n : ℕ => ‖Complex.GammaSeq zp (n + 1)‖) atTop
      (nhds ‖Complex.Gamma zp‖) :=
    (Complex.GammaSeq_tendsto_Gamma zp).norm.comp (tendsto_add_atTop_nat 1)
  have hm : Tendsto (fun n : ℕ => ‖Complex.GammaSeq zm (n + 1)‖) atTop
      (nhds ‖Complex.Gamma zm‖) :=
    (Complex.GammaSeq_tendsto_Gamma zm).norm.comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun n : ℕ => ‖Complex.GammaSeq z0 (n + 1)‖) atTop
      (nhds ‖Complex.Gamma z0‖) :=
    (Complex.GammaSeq_tendsto_Gamma z0).norm.comp (tendsto_add_atTop_nat 1)
  have hlimL := hp.mul hm
  have hc : Tendsto (fun _ : ℕ => Real.exp (32 * u ^ 2)) atTop
      (nhds (Real.exp (32 * u ^ 2))) := tendsto_const_nhds
  have hlimR := hc.mul (h0.pow 2)
  change ‖Complex.Gamma zp‖ * ‖Complex.Gamma zm‖ ≤
    Real.exp (32 * u ^ 2) * ‖Complex.Gamma z0‖ ^ 2
  apply le_of_tendsto_of_tendsto' hlimL hlimR
  intro n
  dsimp only [zp, zm, z0]
  rw [← hquarter]
  exact norm_GammaSeq_symmetric_le t u (n := n + 1) (by omega)

private theorem norm_GammaR_critical (y : ℝ) :
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

private theorem norm_Gamma_quarter_neg_im (y : ℝ) :
    ‖Complex.Gamma ((1 / 4 : ℂ) + ((-y : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖ := by
  let z : ℂ := (1 / 4 : ℂ) + ((-y : ℝ) : ℂ) * I
  have hz : star z = (1 / 4 : ℂ) + (y : ℂ) * I := by
    simp [z]
  calc
    ‖Complex.Gamma z‖ = ‖star (Complex.Gamma z)‖ := by simp
    _ = ‖Complex.Gamma (star z)‖ :=
      (congrArg norm (Complex.Gamma_conj z)).symm
    _ = ‖Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * I)‖ := by rw [hz]

/-- Deligne's real Gamma factor inherits the cancellation-sensitive vertical
pair bound needed by the smooth zeta-squared AFE. -/
theorem norm_GammaR_critical_symmetric_le (t u : ℝ) :
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
        ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ ≤
      Real.exp (8 * u ^ 2) *
        (‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
          ‖Complex.Gammaℝ ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖) := by
  rw [norm_GammaR_critical, norm_GammaR_critical,
    norm_GammaR_critical, norm_GammaR_critical]
  have hgamma := norm_Gamma_symmetric_le (t / 2) (u / 2)
  have hconj := norm_Gamma_quarter_neg_im (t / 2)
  have hconj' :
      ‖Complex.Gamma ((1 / 4 : ℂ) + ((-t / 2 : ℝ) : ℂ) * I)‖ =
        ‖Complex.Gamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ := by
    convert hconj using 1
    all_goals ring_nf
  have hshift := norm_Gamma_quarter_neg_im ((t - u) / 2)
  have hshiftArg : (-t + u) / 2 = -((t - u) / 2) := by ring
  rw [hshiftArg, hshift]
  rw [hconj']
  have hexp : Real.exp (32 * (u / 2) ^ 2) = Real.exp (8 * u ^ 2) := by
    congr 1
    ring
  rw [hexp] at hgamma
  let p := Real.pi ^ (-1 / 4 : ℝ)
  let gp := ‖Complex.Gamma ((1 / 4 : ℂ) + (((t + u) / 2 : ℝ) : ℂ) * I)‖
  let gm := ‖Complex.Gamma ((1 / 4 : ℂ) + (((t - u) / 2 : ℝ) : ℂ) * I)‖
  let g0 := ‖Complex.Gamma ((1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖
  have hgamma' : gp * gm ≤ Real.exp (8 * u ^ 2) * g0 ^ 2 := by
    dsimp only [gp, gm, g0]
    convert hgamma using 1
    all_goals ring_nf
  change p * gp * (p * gm) ≤ Real.exp (8 * u ^ 2) * (p * g0 * (p * g0))
  calc
    p * gp * (p * gm) = p ^ 2 * (gp * gm) := by ring
    _ ≤ p ^ 2 * (Real.exp (8 * u ^ 2) * g0 ^ 2) :=
      mul_le_mul_of_nonneg_left hgamma' (sq_nonneg p)
    _ = Real.exp (8 * u ^ 2) * (p * g0 * (p * g0)) := by ring

end RiemannZeta.GuthMaynard
