import GafniTao.SharpPerronEndpoint
import GafniTao.SharpPerronNearBounds

/-!
# Uniform control of the transition term in sharp Perron

At a general real endpoint one integer can lie arbitrarily close to the
cutoff.  Reciprocal-distance bounds are therefore not uniform.  This module
controls that single transition term directly from the vertical integral,
with a logarithmic (rather than linear) height loss.
-/

open Complex Set

namespace GafniTao

private theorem integral_one_div_add
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    (∫ t : ℝ in 0..T, 1 / (c + t)) = Real.log (c + T) - Real.log c := by
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := T) (f := fun t : ℝ => Real.log (c + t))
    (f' := fun t : ℝ => 1 / (c + t)) (fun t ht => by
      rw [Set.uIcc_of_le hT] at ht
      have hct : c + t ≠ 0 := by linarith [ht.1]
      simpa [one_div] using (Real.hasDerivAt_log hct).comp t
        ((hasDerivAt_const t c).add (hasDerivAt_id t)))
    (by
      have hcont : ContinuousOn (fun t : ℝ => 1 / (c + t))
          (Set.Icc 0 T) :=
        continuousOn_const.div (continuousOn_const.add continuousOn_id)
          (fun t ht hzero => by
            have hz : c + t = 0 := by simpa using hzero
            linarith [ht.1])
      exact hcont.intervalIntegrable_of_Icc hT)
  simpa using hfund

private theorem integral_inv_add_abs
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    (∫ t : ℝ in (-T)..T, 1 / (c + |t|)) =
      2 * (Real.log (c + T) - Real.log c) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  · have hneg := intervalIntegral.integral_comp_neg
        (a := 0) (b := T) (fun t : ℝ => 1 / (c + |t|))
    have hleft : (∫ t : ℝ in (-T)..0, 1 / (c + |t|)) =
        ∫ t : ℝ in 0..T, 1 / (c + t) := by
      calc
        _ = ∫ t : ℝ in 0..T, 1 / (c + |-t|) := by
          simpa only [neg_zero] using hneg.symm
        _ = ∫ t : ℝ in 0..T, 1 / (c + t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hT] at ht
          simp [abs_of_nonneg ht.1]
    have hright : (∫ t : ℝ in 0..T, 1 / (c + |t|)) =
        ∫ t : ℝ in 0..T, 1 / (c + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      simp [abs_of_nonneg ht.1]
    rw [hleft, hright, integral_one_div_add hc hT]
    ring
  · have hcont : Continuous (fun t : ℝ => 1 / (c + |t|)) := by
      exact continuous_const.div
        (continuous_const.add continuous_abs)
        (fun t hzero => by
          have hz : c + |t| = 0 := by simpa using hzero
          linarith [abs_nonneg t])
    exact hcont.intervalIntegrable _ _
  · have hcont : Continuous (fun t : ℝ => 1 / (c + |t|)) := by
      exact continuous_const.div
        (continuous_const.add continuous_abs)
        (fun t hzero => by
          have hz : c + |t| = 0 := by simpa using hzero
          linarith [abs_nonneg t])
    exact hcont.intervalIntegrable _ _

private theorem two_div_add_abs_majorizes_vertical
    {c t : ℝ} (hc : 0 < c) :
    ‖((c : ℂ) + (t : ℂ) * Complex.I)⁻¹‖ ≤ 2 / (c + |t|) := by
  have hdenPos : 0 < c + |t| := add_pos_of_pos_of_nonneg hc (abs_nonneg t)
  have hnormSq : ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hnormNonneg : 0 ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := norm_nonneg _
  have hlinear : c + |t| ≤ 2 * ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    have hsquare : (c + |t|) ^ 2 ≤
        (2 * ‖(c : ℂ) + (t : ℂ) * Complex.I‖) ^ 2 := by
      rw [show (2 * ‖(c : ℂ) + (t : ℂ) * Complex.I‖) ^ 2 =
        4 * ‖(c : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 by ring, hnormSq]
      nlinarith [sq_nonneg (c - |t|), sq_abs t]
    nlinarith
  rw [norm_inv]
  have hnormPos : 0 < ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  rw [inv_eq_one_div]
  rw [div_le_div_iff₀ hnormPos hdenPos]
  simpa using hlinear

/-- A height-logarithmic bound for the scalar Perron kernel, uniform through
the discontinuity. -/
theorem norm_sharpPerronRatioKernel_le_logHeight
    {c T q : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (hq : 0 < q) :
    ‖sharpPerronRatioKernel c T q‖ ≤
      q ^ c * (2 / Real.pi) *
        (Real.log (c + T) - Real.log c) := by
  have hint : IntervalIntegrable
      (fun t : ℝ => (q : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I))
      MeasureTheory.volume (-T) T := by
    have hs : Continuous (fun t : ℝ =>
        (c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have hpow : Continuous (fun t : ℝ =>
        (q : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
      exact Continuous.cpow continuous_const hs
        (fun _ => Complex.ofReal_mem_slitPlane.mpr hq)
    exact (hpow.div hs (fun t hzero => by
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith)).intervalIntegrable _ _
  have hscalar : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [sharpPerronRatioKernel, norm_mul, hscalar]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t in (-T)..T,
          (q : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (1 / (2 * Real.pi)) *
          ∫ t in (-T)..T, q ^ c * (2 / (c + |t|)) := by
      gcongr
      refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ ?_
      · filter_upwards with t
        intro _ht
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hq]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, zero_mul, Complex.I_re, mul_zero, sub_zero]
        simp only [add_zero]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [norm_inv] using
            (two_div_add_abs_majorizes_vertical (t := t) hc))
          (Real.rpow_nonneg hq.le c)
      · have hcont : Continuous (fun t : ℝ =>
            q ^ c * (2 / (c + |t|))) := by
          exact continuous_const.mul (continuous_const.div
            (continuous_const.add continuous_abs)
            (fun t hzero => by
              have hz : c + |t| = 0 := by simpa using hzero
              linarith [abs_nonneg t]))
        exact hcont.intervalIntegrable _ _
    _ = q ^ c * (2 / Real.pi) *
          (Real.log (c + T) - Real.log c) := by
      rw [intervalIntegral.integral_const_mul,
        show (∫ x : ℝ in (-T)..T, 2 / (c + |x|)) =
          2 * (∫ x : ℝ in (-T)..T, 1 / (c + |x|)) by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t _ht
            ring,
        integral_inv_add_abs hc hT]
      ring

/-- The one (or at most two, before tie-breaking) integer terms within unit
distance of a real cutoff are controlled directly, without a reciprocal
distance singularity. -/
theorem norm_vonMangoldt_cutoffError_le_transition
    {T x : ℝ} {n : ℕ} (hx : 2 ≤ x) (hT : 0 ≤ T)
    (hn : 1 ≤ n) (hnear : |x - (n : ℝ)| < 1) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel (sharpPerronAbscissa x) T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff x n‖ ≤
      ArithmeticFunction.vonMangoldt n *
        (sharpPerronRatioBound * (2 / Real.pi) *
          (Real.log (sharpPerronAbscissa x + T) -
            Real.log (sharpPerronAbscissa x)) + 1) := by
  have hxPos : 0 < x := by linarith
  have hnPos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hnLower : x / 2 < (n : ℝ) := by
    rw [abs_lt] at hnear
    linarith
  have hnUpper : (n : ℝ) < 2 * x := by
    rw [abs_lt] at hnear
    linarith
  have hratioPos : 0 < x / (n : ℝ) := div_pos hxPos hnPos
  have hratioTwo : x / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hnPos]
    linarith
  have hcPos := sharpPerronAbscissa_pos (y := x) (by linarith [hx])
  have hpow := rpow_sharpPerronAbscissa_le_ratioBound
    hx hratioPos.le hratioTwo
  have hkernel := norm_sharpPerronRatioKernel_le_logHeight
    hcPos hT hratioPos
  have hkernel' :
      ‖sharpPerronKernel (sharpPerronAbscissa x) T x n‖ ≤
        sharpPerronRatioBound * (2 / Real.pi) *
          (Real.log (sharpPerronAbscissa x + T) -
            Real.log (sharpPerronAbscissa x)) := by
    rw [sharpPerronKernel_eq_ratioKernel hxPos hn]
    refine hkernel.trans ?_
    have hlog : 0 ≤ Real.log (sharpPerronAbscissa x + T) -
        Real.log (sharpPerronAbscissa x) := by
      rw [sub_nonneg, Real.log_le_log_iff hcPos (by linarith)]
      linarith
    have hfactor : 0 ≤ (2 / Real.pi) *
        (Real.log (sharpPerronAbscissa x + T) -
          Real.log (sharpPerronAbscissa x)) :=
      mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) hlog
    calc
      (x / (n : ℝ)) ^ sharpPerronAbscissa x * (2 / Real.pi) *
          (Real.log (sharpPerronAbscissa x + T) -
            Real.log (sharpPerronAbscissa x)) =
        (x / (n : ℝ)) ^ sharpPerronAbscissa x *
          ((2 / Real.pi) *
            (Real.log (sharpPerronAbscissa x + T) -
              Real.log (sharpPerronAbscissa x))) := by ring
      _ ≤ sharpPerronRatioBound *
          ((2 / Real.pi) *
            (Real.log (sharpPerronAbscissa x + T) -
              Real.log (sharpPerronAbscissa x))) :=
        mul_le_mul_of_nonneg_right hpow hfactor
      _ = sharpPerronRatioBound * (2 / Real.pi) *
          (Real.log (sharpPerronAbscissa x + T) -
            Real.log (sharpPerronAbscissa x)) := by ring
  have hcut : ‖sharpPerronCutoff x n‖ ≤ (1 : ℝ) := by
    unfold sharpPerronCutoff
    split <;> norm_num
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  calc
    ‖sharpPerronKernel (sharpPerronAbscissa x) T x n -
        sharpPerronCutoff x n‖ ≤
      ‖sharpPerronKernel (sharpPerronAbscissa x) T x n‖ +
        ‖sharpPerronCutoff x n‖ := norm_sub_le _ _
    _ ≤ sharpPerronRatioBound * (2 / Real.pi) *
          (Real.log (sharpPerronAbscissa x + T) -
            Real.log (sharpPerronAbscissa x)) + 1 :=
      add_le_add hkernel' hcut

end GafniTao
