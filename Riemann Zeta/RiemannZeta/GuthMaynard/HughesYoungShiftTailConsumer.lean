import RiemannZeta.GuthMaynard.HughesYoungNativeCentralAssembly
import RiemannZeta.GuthMaynard.HughesYoungShiftTail

open Asymptotics Complex Filter Finset MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native Hughes--Young consumer of the quantitative shift tail

This module joins the source-level equation-(84) tail estimate to the exact
finite signed shift window used by the native DFI assembly.
-/

/-- Exact signed finite-window split for the equation-(84) source integrals. -/
theorem sum_hughesYoungFiniteSignedEquation84SourceIntegral_shiftInterval_eq
    (T t : ℝ) (h k a b B : ℕ) :
    (∑ r ∈ hughesYoungShiftInterval a b B B,
      hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r) =
      (∑ n ∈ Finset.Icc 1 (a * B),
        (hughesYoungHeightWeight T t : ℂ) *
          ∫ u : ℝ,
            hughesYoungEquation84PositiveContourSeries T t h k a b n
              ((1 : ℂ) + (u : ℂ) * I)) +
      ∑ n ∈ Finset.Icc 1 (b * B),
        (hughesYoungHeightWeight T t : ℂ) *
          ∫ u : ℝ,
            hughesYoungEquation84NegativeContourSeries T t h k a b n
              ((1 : ℂ) + (u : ℂ) * I) := by
  classical
  unfold hughesYoungShiftInterval
  have hzero : (∑ r ∈ Finset.Icc (-(b * B : ℤ)) (a * B : ℤ),
      hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r) =
      ∑ r ∈ Finset.Icc (-(b * B : ℤ)) (a * B : ℤ),
        if r = 0 then 0
        else hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r := by
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hr0 : r = 0
    · subst r
      simp [hughesYoungFiniteSignedEquation84SourceIntegral]
    · simp [hr0]
  rw [hzero]
  change (∑ r ∈ Finset.Icc (-(((b * B : ℕ) : ℤ))) (((a * B : ℕ) : ℤ)),
      if r = 0 then 0
      else hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r) = _
  rw [sum_int_Icc_ite_zero_eq_positive_add_negative]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    simp [hughesYoungFiniteSignedEquation84SourceIntegral, hn0]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      simp only [Finset.mem_Icc] at hn
      omega
    simp [hughesYoungFiniteSignedEquation84SourceIntegral, hn0]

/-- The finite native signed window is exactly the height weight times the
two retained equation-(84) source prefixes. -/
theorem sum_hughesYoungFiniteSignedEquation84SourceIntegral_eq_prefixIntegrals
    (T t : ℝ) (h k : ℕ) {a b B : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∑ r ∈ hughesYoungShiftInterval a b B B,
      hughesYoungFiniteSignedEquation84SourceIntegral T t h k a b r) =
      (hughesYoungHeightWeight T t : ℂ) *
        ((∫ u : ℝ,
            hughesYoungEquation84PositiveContourTermPrefix
              T t h k a b u (a * B : ℕ)) +
          ∫ u : ℝ,
            hughesYoungEquation84NegativeContourTermPrefix
              T t h k a b u (b * B : ℕ)) := by
  rw [sum_hughesYoungFiniteSignedEquation84SourceIntegral_shiftInterval_eq]
  have hposInt :
      (∑ n ∈ Finset.Icc 1 (a * B),
        ∫ u : ℝ,
          hughesYoungEquation84PositiveContourSeries T t h k a b n
            ((1 : ℂ) + (u : ℂ) * I)) =
        ∫ u : ℝ, ∑ n ∈ Finset.Icc 1 (a * B),
          hughesYoungEquation84PositiveContourSeries T t h k a b n
            ((1 : ℂ) + (u : ℂ) * I) := by
    symm
    apply integral_finsetSum
    intro n hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact integrable_hughesYoungEquation84PositiveContourSeries_vertical
      T t h k a b n ha hb hnpos (by norm_num) (by norm_num)
  have hnegInt :
      (∑ n ∈ Finset.Icc 1 (b * B),
        ∫ u : ℝ,
          hughesYoungEquation84NegativeContourSeries T t h k a b n
            ((1 : ℂ) + (u : ℂ) * I)) =
        ∫ u : ℝ, ∑ n ∈ Finset.Icc 1 (b * B),
          hughesYoungEquation84NegativeContourSeries T t h k a b n
            ((1 : ℂ) + (u : ℂ) * I) := by
    symm
    apply integral_finsetSum
    intro n hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact integrable_hughesYoungEquation84NegativeContourSeries_vertical
      T t h k a b n ha hb hnpos (by norm_num) (by norm_num)
  simp_rw [← Finset.mul_sum]
  rw [hposInt, hnegInt]
  rw [show (∫ u : ℝ, ∑ n ∈ Finset.Icc 1 (a * B),
      hughesYoungEquation84PositiveContourSeries T t h k a b n
        ((1 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungEquation84PositiveContourTermPrefix
        T t h k a b u (a * B : ℕ) by
    apply integral_congr_ae
    filter_upwards [] with u
    exact sum_hughesYoungEquation84PositiveContourSeries_Icc_eq_prefix
      T t h k ha hb hab u (a * B)
        (by norm_num : (0 : ℝ) < 1 / 8)
        (by norm_num : (1 / 8 : ℝ) < 1 / 4),
    show (∫ u : ℝ, ∑ n ∈ Finset.Icc 1 (b * B),
      hughesYoungEquation84NegativeContourSeries T t h k a b n
        ((1 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungEquation84NegativeContourTermPrefix
        T t h k a b u (b * B : ℕ) by
    apply integral_congr_ae
    filter_upwards [] with u
    exact sum_hughesYoungEquation84NegativeContourSeries_Icc_eq_prefix
      T t h k ha hb hab u (b * B)
        (by norm_num : (0 : ℝ) < 1 / 8)
        (by norm_num : (1 / 8 : ℝ) < 1 / 4)]
  ring

theorem integrable_hughesYoungEquation84PositiveContourTermPrefix_nat
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (L : ℕ) :
    Integrable (fun u : ℝ =>
      hughesYoungEquation84PositiveContourTermPrefix
        T t h k a b u (L : ℝ)) := by
  have hs : Integrable (fun u : ℝ =>
      ∑ n ∈ Finset.Icc 1 L,
        hughesYoungEquation84PositiveContourSeries T t h k a b n
          ((1 : ℂ) + (u : ℂ) * I)) := by
    apply integrable_finsetSum
    intro n hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact integrable_hughesYoungEquation84PositiveContourSeries_vertical
      T t h k a b n ha hb hnpos (by norm_num) (by norm_num)
  apply hs.congr
  filter_upwards [] with u
  exact sum_hughesYoungEquation84PositiveContourSeries_Icc_eq_prefix
    T t h k ha hb hab u L
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)

theorem integrable_hughesYoungEquation84NegativeContourTermPrefix_nat
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (L : ℕ) :
    Integrable (fun u : ℝ =>
      hughesYoungEquation84NegativeContourTermPrefix
        T t h k a b u (L : ℝ)) := by
  have hs : Integrable (fun u : ℝ =>
      ∑ n ∈ Finset.Icc 1 L,
        hughesYoungEquation84NegativeContourSeries T t h k a b n
          ((1 : ℂ) + (u : ℂ) * I)) := by
    apply integrable_finsetSum
    intro n hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    exact integrable_hughesYoungEquation84NegativeContourSeries_vertical
      T t h k a b n ha hb hnpos (by norm_num) (by norm_num)
  apply hs.congr
  filter_upwards [] with u
  exact sum_hughesYoungEquation84NegativeContourSeries_Icc_eq_prefix
    T t h k ha hb hab u L
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)

theorem integrable_hughesYoungEquation84PositiveContourTermShiftTail_nat
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (L : ℕ) :
    Integrable (fun u : ℝ =>
      hughesYoungEquation84PositiveContourTermShiftTail
        T t h k a b u (L : ℝ)) := by
  have hc := integrable_hughesYoungEquation84CompletePositiveSourceLine
    T t h k ha hb hab (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  have hp := integrable_hughesYoungEquation84PositiveContourTermPrefix_nat
    T t h k ha hb hab L
  apply (hc.sub hp).congr
  filter_upwards [] with u
  change hughesYoungEquation84CompletePositiveSourceLine T t h k a b u -
      hughesYoungEquation84PositiveContourTermPrefix T t h k a b u (L : ℝ) = _
  rw [hughesYoungEquation84CompletePositiveSourceLine_eq_contourPrefix_add_tail
    T t h k ha hb hab u (L : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)]
  ring

theorem integrable_hughesYoungEquation84NegativeContourTermShiftTail_nat
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (L : ℕ) :
    Integrable (fun u : ℝ =>
      hughesYoungEquation84NegativeContourTermShiftTail
        T t h k a b u (L : ℝ)) := by
  have hc := integrable_hughesYoungEquation84CompleteNegativeSourceLine
    T t h k ha hb hab (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  have hp := integrable_hughesYoungEquation84NegativeContourTermPrefix_nat
    T t h k ha hb hab L
  apply (hc.sub hp).congr
  filter_upwards [] with u
  change hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u -
      hughesYoungEquation84NegativeContourTermPrefix T t h k a b u (L : ℝ) = _
  rw [hughesYoungEquation84CompleteNegativeSourceLine_eq_contourPrefix_add_tail
    T t h k ha hb hab u (L : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)]
  ring

/-- The positive equation-(84) archimedean envelope after the arithmetic
shift sum has been factored out.  Keeping this as a separate real-valued
function is what allows the negative power of the terminal shift cutoff to
survive the contour integral. -/
noncomputable def hughesYoungEquation84PositiveShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) : ℂ :=
  ((‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ *
    (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
      ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
      ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
      ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖) : ℝ) : ℂ)

/-- The corresponding negative-sign archimedean envelope. -/
noncomputable def hughesYoungEquation84NegativeShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) : ℂ :=
  ((‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ *
    (‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
      ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
      ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
      ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) : ℝ) : ℂ)

theorem norm_hughesYoungEquation84PositiveShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) :
    ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b u‖ =
      ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ *
        (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖) := by
  unfold hughesYoungEquation84PositiveShiftTailEnvelope
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

theorem norm_hughesYoungEquation84NegativeShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) (u : ℝ) :
    ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b u‖ =
      ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ *
        (‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) := by
  unfold hughesYoungEquation84NegativeShiftTailEnvelope
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

/-- On the source line the reduced Mellin outer factor has an exact norm;
the contour ordinate and physical height contribute only phases. -/
theorem norm_hughesYoungEquation84CompletePositiveOuter_reduced_eq
    (T t : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (u : ℝ) :
    ‖hughesYoungEquation84CompletePositiveOuter T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) := by
  have h := norm_inv_reduced_mul_hughesYoungReducedMellinStaticComplex_eq
    hh hk T t 1 u
  unfold hughesYoungEquation84CompletePositiveOuter
  norm_num at h ⊢
  simpa only [Nat.cast_mul] using h

theorem norm_hughesYoungEquation84CompleteNegativeOuter_reduced_eq
    (T t : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (u : ℝ) :
    ‖hughesYoungEquation84CompleteNegativeOuter T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
        (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) := by
  rw [show hughesYoungEquation84CompleteNegativeOuter T t h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u =
        hughesYoungEquation84CompletePositiveOuter T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u by
    unfold hughesYoungEquation84CompleteNegativeOuter
      hughesYoungEquation84CompletePositiveOuter
    ring]
  exact norm_hughesYoungEquation84CompletePositiveOuter_reduced_eq
    T t hh hk u

theorem continuous_hughesYoungEquation84PositiveShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) :
    Continuous (hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b) := by
  unfold hughesYoungEquation84PositiveShiftTailEnvelope
    hughesYoungEquation84CompletePositiveOuter
  exact Complex.continuous_ofReal.comp ((continuous_const.mul
    (continuous_hughesYoungReducedMellinStaticComplex_sourceLine T t h k)).norm.mul
      (((continuous_hughesYoungEquation84Kernel00_sourceLine t).norm.add
        (continuous_hughesYoungEquation84Kernel10_sourceLine t).norm).add
        (continuous_hughesYoungEquation84Kernel01_sourceLine t).norm |>.add
        (continuous_hughesYoungEquation84Kernel11_sourceLine t).norm))

theorem continuous_hughesYoungEquation84NegativeShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) :
    Continuous (hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b) := by
  unfold hughesYoungEquation84NegativeShiftTailEnvelope
    hughesYoungEquation84CompleteNegativeOuter
  exact Complex.continuous_ofReal.comp ((continuous_const.mul
    (continuous_hughesYoungReducedMellinStaticComplex_sourceLine T t h k)).norm.mul
      (((continuous_hughesYoungEquation84Kernel00_sourceLine (-t)).norm.add
        (continuous_hughesYoungEquation84Kernel10_sourceLine (-t)).norm).add
        (continuous_hughesYoungEquation84Kernel01_sourceLine (-t)).norm |>.add
        (continuous_hughesYoungEquation84Kernel11_sourceLine (-t)).norm))

/-! ## Cancellation between the two ordinary Gamma factors -/

/-- Translating a real hyperbolic cosine costs at most the exponential of
the translation.  This elementary inequality is the exact real-variable
input needed to keep the two ordinary Gamma factors in equation (84)
paired. -/
theorem real_cosh_add_le_exp_abs_mul_cosh (x d : ℝ) :
    Real.cosh (x + d) ≤ Real.exp |d| * Real.cosh x := by
  have hplus : Real.exp d ≤ Real.exp |d| :=
    Real.exp_le_exp.mpr (le_abs_self d)
  have hminus : Real.exp (-d) ≤ Real.exp |d| :=
    Real.exp_le_exp.mpr (neg_le_abs d)
  rw [Real.cosh_eq, Real.cosh_eq]
  rw [Real.exp_add, show -(x + d) = -x + -d by ring, Real.exp_add]
  have hx : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have hnx : 0 ≤ Real.exp (-x) := (Real.exp_pos (-x)).le
  calc
    (Real.exp x * Real.exp d + Real.exp (-x) * Real.exp (-d)) / 2 ≤
        (Real.exp x * Real.exp |d| + Real.exp (-x) * Real.exp |d|) / 2 := by
          gcongr
    _ = Real.exp |d| * ((Real.exp x + Real.exp (-x)) / 2) := by ring

/-- On the equation-(84) source line, the reciprocal Gamma factor in the
beta kernel cancels against the Gamma factor inside the regularized moving
pole.  The quotient is uniform in the physical ordinate `t`; only the
contour ordinate `u` remains. -/
theorem norm_Gamma_half_t_sub_u_div_threeHalf_t_add_u_le (t u : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I) /
        Complex.Gamma ((3 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ ≤
      2 * Real.exp (Real.pi * |u|) := by
  let A : ℝ :=
    ‖Complex.Gamma ((1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I)‖
  let B : ℝ :=
    ‖Complex.Gamma ((3 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖
  let X : ℝ := Real.cosh (Real.pi * (t - u))
  let Y : ℝ := Real.cosh (Real.pi * (t + u))
  let E : ℝ := Real.exp (2 * Real.pi * |u|)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hX : 0 < X := by dsimp only [X]; exact Real.cosh_pos _
  have hY : 0 < Y := by dsimp only [Y]; exact Real.cosh_pos _
  have hE : 0 < E := by dsimp only [E]; positivity
  have hA2 : A ^ 2 = Real.pi / X := by
    simpa only [A, X] using Gamma_half_add_mul_I_norm_sq (t - u)
  have hB2 : B ^ 2 = ((1 / 4 : ℝ) + (t + u) ^ 2) * (Real.pi / Y) := by
    simpa only [B, Y] using Gamma_three_half_add_mul_I_norm_sq (t + u)
  have hShift := real_cosh_add_le_exp_abs_mul_cosh
    (Real.pi * (t - u)) (2 * Real.pi * u)
  have hArg : Real.pi * (t - u) + 2 * Real.pi * u =
      Real.pi * (t + u) := by ring
  have hAbs : |2 * Real.pi * u| = 2 * Real.pi * |u| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
  rw [hArg, hAbs] at hShift
  change Y ≤ E * X at hShift
  have hInv : X⁻¹ ≤ E * Y⁻¹ := by
    calc
      X⁻¹ = Y * (X * Y)⁻¹ := by field_simp
      _ ≤ (E * X) * (X * Y)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hShift (inv_nonneg.mpr (mul_nonneg hX.le hY.le))
      _ = E * Y⁻¹ := by field_simp
  have hQuarter : (1 : ℝ) ≤ 4 * ((1 / 4 : ℝ) + (t + u) ^ 2) := by
    nlinarith [sq_nonneg (t + u)]
  have hSquare : A ^ 2 ≤
      (2 * Real.exp (Real.pi * |u|)) ^ 2 * B ^ 2 := by
    rw [hA2, hB2, div_eq_mul_inv, div_eq_mul_inv]
    have hExpSq : (2 * Real.exp (Real.pi * |u|)) ^ 2 = 4 * E := by
      dsimp only [E]
      rw [mul_pow, show Real.exp (Real.pi * |u|) ^ 2 =
          Real.exp (2 * Real.pi * |u|) by
        rw [← Real.exp_nat_mul]
        congr 1
        ring]
      norm_num
    rw [hExpSq]
    calc
      Real.pi * X⁻¹ ≤ Real.pi * (E * Y⁻¹) :=
        mul_le_mul_of_nonneg_left hInv Real.pi_pos.le
      _ ≤ (4 * E) * (((1 / 4 : ℝ) + (t + u) ^ 2) *
          (Real.pi * Y⁻¹)) := by
        have hnonneg : 0 ≤ E * (Real.pi * Y⁻¹) := by positivity
        nlinarith
      _ = 4 * E *
          (((1 / 4 : ℝ) + (t + u) ^ 2) * (Real.pi * Y⁻¹)) := by ring
  rw [norm_div]
  exact (sq_le_sq₀ (div_nonneg hA hB.le)
    (mul_nonneg (by norm_num) (Real.exp_pos _).le)).mp (by
      rw [div_pow, div_le_iff₀ (pow_pos hB 2)]
      simpa only [A, B] using hSquare)

set_option maxHeartbeats 1000000 in
/-- Cancellation-preserving source-line estimate for the beta kernel.  In
contrast with a separate reciprocal-Gamma estimate, this bound is uniform
in `t`: the regularized Gamma factor at `1/2+i(t-u)` is divided by the
Gamma factor at `3/2+i(t+u)` before norms are estimated. -/
theorem exists_norm_hughesYoungEquation84RegularizedBetaKernel_sourceLine_joint_le
    (CX COne : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ),
      ‖hughesYoungEquation84RegularizedBetaKernel t
          ((1 : ℂ) + (u : ℂ) * I) CX COne‖ ≤
        C * Real.exp (Real.pi * |u|) * (3 + |t| + |u|) ^ 3 := by
  obtain ⟨G₂, hG₂, hGamma₂⟩ := exists_uniform_norm_Gamma_vertical_strip
    (a := (2 : ℝ)) (b := (2 : ℝ)) (by norm_num)
  obtain ⟨D₁, hD₁, hDigamma₁⟩ :=
    exists_uniform_norm_digamma_vertical_strip_linear
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num)
  obtain ⟨D₃, hD₃, hDigamma₃⟩ :=
    exists_uniform_norm_digamma_vertical_strip_linear
      (a := (3 / 2 : ℝ)) (b := (3 / 2 : ℝ)) (by norm_num)
  obtain ⟨D₂, hD₂, hDigamma₂⟩ :=
    exists_uniform_norm_digamma_vertical_strip_linear
      (a := (2 : ℝ)) (b := (2 : ℝ)) (by norm_num)
  obtain ⟨P, hP, hPoly⟩ :=
    exists_uniform_norm_hughesYoungPolygamma_one_horizontal_le
      (c₀ := (1 : ℝ)) (c₁ := (1 : ℝ)) (by norm_num)
  let K : ℝ := D₁ + D₃ + 2 * D₂ + ‖CX‖ + ‖COne‖ + P + 2
  let C : ℝ := 2 * G₂ * (2 * K ^ 2 + K + P + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u
  let w : ℂ := (1 : ℂ) + (u : ℂ) * I
  let p : ℂ := afeCriticalPoint t + w
  let z : ℂ := afeCriticalPoint t - w
  let R : ℝ := 3 + |t| + |u|
  let U : ℂ := -Complex.digamma (2 * w) + CX
  let V : ℂ := Complex.digamma p - Complex.digamma (2 * w) + COne
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith [abs_nonneg t, abs_nonneg u]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have htu : |t - u| + 2 ≤ R := by
    have htri : |t - u| ≤ |t| + |u| := abs_sub t u
    dsimp only [R]
    linarith
  have htpu : |t + u| + 2 ≤ R := by
    have htri : |t + u| ≤ |t| + |u| := abs_add_le t u
    dsimp only [R]
    linarith
  have hu₂ : |2 * u| + 2 ≤ 2 * R := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp only [R]
    linarith [abs_nonneg t, abs_nonneg u]
  have hGammaTwo : ‖Complex.Gamma (2 * w)‖ ≤ G₂ := by
    have harg : 2 * w = (2 : ℂ) + ((2 * u : ℝ) : ℂ) * I := by
      dsimp only [w]
      push_cast
      ring
    rw [harg]
    exact hGamma₂ 2 (2 * u) ⟨le_rfl, le_rfl⟩
  have hDigZ : ‖Complex.digamma (z + 1)‖ ≤ D₁ * R := by
    have harg : z + 1 = (1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I := by
      dsimp only [z, w, afeCriticalPoint]
      push_cast
      ring
    rw [harg]
    have hraw := hDigamma₁ (1 / 2) (t - u) ⟨le_rfl, le_rfl⟩
    norm_num at hraw ⊢
    exact hraw.trans (mul_le_mul_of_nonneg_left htu hD₁.le)
  have hDigP : ‖Complex.digamma p‖ ≤ D₃ * R := by
    have harg : p = (3 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I := by
      dsimp only [p, w, afeCriticalPoint]
      push_cast
      ring
    rw [harg]
    have hraw := hDigamma₃ (3 / 2) (t + u) ⟨le_rfl, le_rfl⟩
    norm_num at hraw ⊢
    exact hraw.trans (mul_le_mul_of_nonneg_left htpu hD₃.le)
  have hDigTwo : ‖Complex.digamma (2 * w)‖ ≤ 2 * D₂ * R := by
    have harg : 2 * w = (2 : ℂ) + ((2 * u : ℝ) : ℂ) * I := by
      dsimp only [w]
      push_cast
      ring
    rw [harg]
    calc
      ‖Complex.digamma ((2 : ℂ) + ((2 * u : ℝ) : ℂ) * I)‖ ≤
          D₂ * (|2 * u| + 2) := hDigamma₂ 2 (2 * u) ⟨le_rfl, le_rfl⟩
      _ ≤ D₂ * (2 * R) := mul_le_mul_of_nonneg_left hu₂ hD₂.le
      _ = 2 * D₂ * R := by ring
  have hPolyOne : ‖hughesYoungPolygammaSeries 1 (2 * w)‖ ≤ P := by
    have h := hPoly u 1 ⟨le_rfl, le_rfl⟩
    dsimp only [w]
    convert h using 1
  have hzNorm : ‖z‖ ≤ R := by
    have hzarg : z = (-1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I := by
      dsimp only [z, w, afeCriticalPoint]
      push_cast
      ring
    rw [hzarg]
    calc
      ‖(-1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I‖ ≤
          ‖(-1 / 2 : ℂ)‖ + ‖((t - u : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + |t - u| := by
        rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ R := by linarith
  have hU : ‖U‖ ≤ K * R := by
    calc
      ‖U‖ = ‖-Complex.digamma (2 * w) + CX‖ := by rfl
      _ ≤ ‖Complex.digamma (2 * w)‖ + ‖CX‖ := by
        simpa only [norm_neg] using norm_add_le (-Complex.digamma (2 * w)) CX
      _ ≤ 2 * D₂ * R + ‖CX‖ := by gcongr
      _ ≤ K * R := by
        dsimp only [K]
        nlinarith [hD₁, hD₃, hD₂, hP, hR1, norm_nonneg CX, norm_nonneg COne]
  have hV : ‖V‖ ≤ K * R := by
    calc
      ‖V‖ ≤ ‖Complex.digamma p‖ + ‖Complex.digamma (2 * w)‖ + ‖COne‖ := by
        dsimp only [V]
        have hsub := norm_sub_le (Complex.digamma p) (Complex.digamma (2 * w))
        linarith [norm_add_le
          (Complex.digamma p - Complex.digamma (2 * w)) COne]
      _ ≤ D₃ * R + 2 * D₂ * R + ‖COne‖ := by gcongr
      _ ≤ K * R := by
        dsimp only [K]
        nlinarith [hD₁, hD₃, hD₂, hP, hR1, norm_nonneg CX, norm_nonneg COne]
  have hZPsi : ‖z * Complex.digamma (z + 1) - 1‖ ≤ K * R ^ 2 := by
    calc
      _ ≤ ‖z‖ * ‖Complex.digamma (z + 1)‖ + 1 := by
        simpa only [norm_mul, norm_one] using
          norm_sub_le (z * Complex.digamma (z + 1)) 1
      _ ≤ R * (D₁ * R) + 1 := by gcongr
      _ ≤ K * R ^ 2 := by
        dsimp only [K]
        nlinarith [hD₁, hD₃, hD₂, hP, hR1, sq_nonneg R,
          norm_nonneg CX, norm_nonneg COne]
  have hBracket :
      ‖(z * Complex.digamma (z + 1) - 1) * V +
          z * (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ ≤
        (2 * K ^ 2 + K + P + 1) * R ^ 3 := by
    calc
      _ ≤ ‖z * Complex.digamma (z + 1) - 1‖ * ‖V‖ +
          ‖z‖ * (‖U‖ * ‖V‖ + ‖hughesYoungPolygammaSeries 1 (2 * w)‖) := by
        calc
          _ ≤ ‖(z * Complex.digamma (z + 1) - 1) * V‖ +
              ‖z * (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ :=
                norm_add_le _ _
          _ = ‖z * Complex.digamma (z + 1) - 1‖ * ‖V‖ +
              ‖z‖ * ‖U * V + hughesYoungPolygammaSeries 1 (2 * w)‖ := by
                rw [norm_mul, norm_mul]
          _ ≤ _ := by
            gcongr
            exact (norm_add_le _ _).trans <| by rw [norm_mul]
      _ ≤ (K * R ^ 2) * (K * R) +
          R * ((K * R) * (K * R) + P) := by gcongr
      _ ≤ (2 * K ^ 2 + K + P + 1) * R ^ 3 := by
        have hR3 : R ≤ R ^ 3 := by nlinarith [sq_nonneg R]
        have hPR : P * R ≤ P * R ^ 3 :=
          mul_le_mul_of_nonneg_left hR3 hP.le
        ring_nf at hPR ⊢
        nlinarith [hK, hP, sq_nonneg K, sq_nonneg R]
  have hGammaPair :
      ‖Complex.Gamma (z + 1) / Complex.Gamma p‖ ≤
        2 * Real.exp (Real.pi * |u|) := by
    have hzarg : z + 1 = (1 / 2 : ℂ) + ((t - u : ℝ) : ℂ) * I := by
      dsimp only [z, w, afeCriticalPoint]
      push_cast
      ring
    have hparg : p = (3 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I := by
      dsimp only [p, w, afeCriticalPoint]
      push_cast
      ring
    rw [hzarg, hparg]
    exact norm_Gamma_half_t_sub_u_div_threeHalf_t_add_u_le t u
  have hfactor :
      hughesYoungEquation84RegularizedBetaKernel t w CX COne =
        Complex.Gamma (2 * w) *
          (Complex.Gamma (z + 1) / Complex.Gamma p) *
          ((z * Complex.digamma (z + 1) - 1) * V +
            z * (U * V + hughesYoungPolygammaSeries 1 (2 * w))) := by
    unfold hughesYoungEquation84RegularizedBetaKernel
      hughesYoungRegularizedGammaDigamma hughesYoungRegularizedGamma
    dsimp only [z, p, U, V]
    simp only [div_eq_mul_inv]
    ring
  rw [hfactor, norm_mul, norm_mul]
  calc
    _ ≤ G₂ * (2 * Real.exp (Real.pi * |u|)) *
        ((2 * K ^ 2 + K + P + 1) * R ^ 3) := by gcongr
    _ = C * Real.exp (Real.pi * |u|) * (3 + |t| + |u|) ^ 3 := by
      dsimp only [C, R]
      ring

set_option maxHeartbeats 1000000 in
/-- On the equation-(84) source line the six shifted pole factors cancel
six of the eight critical-line factors in `afePoleNormalization`.  Keeping
this quotient intact removes the spurious sixth power of the physical
height which results from bounding the numerator and denominator
separately. -/
theorem norm_hughesYoungEquation84NormalizedCorePolynomial_sourceLine_le
    (t u : ℝ) :
    let w : ℂ := (1 : ℂ) + (u : ℂ) * I
    let p : ℂ := afeCriticalPoint t + w
    let q : ℂ := afeCriticalPoint (-t) + w
    ‖((p * (1 - p)) ^ 2 * q ^ 2) * (afePoleNormalization t)⁻¹‖ ≤
      2916 * (1 + |u|) ^ 6 := by
  dsimp only
  let s : ℂ := afeCriticalPoint t
  let sbar : ℂ := afeCriticalPoint (-t)
  let w : ℂ := (1 : ℂ) + (u : ℂ) * I
  let L : ℝ := 1 + |u|
  let B : ℝ := ‖s‖
  have hL : 1 ≤ L := by dsimp only [L]; linarith [abs_nonneg u]
  have hw : ‖w‖ ≤ L := by
    calc
      ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖(u : ℂ) * I‖ := by
        dsimp only [w]
        exact norm_add_le _ _
      _ = L := by simp [L, Real.norm_eq_abs]
  have hB : (1 / 2 : ℝ) ≤ B := by
    have hre := Complex.abs_re_le_norm s
    have hsre : s.re = 1 / 2 := by simp [s, afeCriticalPoint]
    rw [hsre, abs_of_nonneg (by norm_num)] at hre
    simpa only [B] using hre
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hsym : ‖sbar‖ = B := by
    dsimp only [sbar, B, s]
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [afeCriticalPoint, Complex.normSq]
  have hshift (z v : ℂ) (hz : ‖z‖ = B) (hv : ‖v‖ ≤ L) :
      ‖z + v‖ ≤ 3 * L * B := by
    have hproduct : 0 ≤ (L - 1) * (B - 1 / 2) :=
      mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hB)
    calc
      ‖z + v‖ ≤ ‖z‖ + ‖v‖ := norm_add_le _ _
      _ ≤ B + L := by rw [hz]; gcongr
      _ ≤ 3 * L * B := by nlinarith
  have hshiftSub (z v : ℂ) (hz : ‖z‖ = B) (hv : ‖v‖ ≤ L) :
      ‖z - v‖ ≤ 3 * L * B := by
    have hproduct : 0 ≤ (L - 1) * (B - 1 / 2) :=
      mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hB)
    calc
      ‖z - v‖ ≤ ‖z‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ B + L := by rw [hz]; gcongr
      _ ≤ 3 * L * B := by nlinarith
  have hp : ‖s + w‖ ≤ 3 * L * B := hshift s w rfl hw
  have hOneP : ‖1 - (s + w)‖ ≤ 3 * L * B := by
    rw [show 1 - (s + w) = (1 - s) - w by ring]
    have hone : 1 - s = sbar := by
      dsimp only [s, sbar]
      exact one_sub_afeCriticalPoint t
    rw [hone]
    exact hshiftSub sbar w hsym hw
  have hq : ‖sbar + w‖ ≤ 3 * L * B := hshift sbar w hsym hw
  have hPoleNorm : ‖afePoleNormalization t‖ = B ^ 8 := by
    unfold afePoleNormalization
    rw [norm_pow]
    simp only [norm_mul]
    have hone : ‖1 - afeCriticalPoint t‖ = B := by
      rw [one_sub_afeCriticalPoint]
      exact hsym
    have honebar : ‖1 - afeCriticalPoint (-t)‖ = B := by
      rw [one_sub_afeCriticalPoint, neg_neg]
    dsimp only [sbar] at hsym
    dsimp only [B, s]
    rw [hone, hsym, honebar]
    ring
  have hInvNorm : ‖(afePoleNormalization t)⁻¹‖ = (B ^ 8)⁻¹ := by
    rw [norm_inv, hPoleNorm]
  have hNumerator :
      ‖((s + w) * (1 - (s + w))) ^ 2 * (sbar + w) ^ 2‖ ≤
        (3 * L * B) ^ 6 := by
    simp only [norm_mul, norm_pow]
    calc
      (‖s + w‖ * ‖1 - (s + w)‖) ^ 2 * ‖sbar + w‖ ^ 2 ≤
          ((3 * L * B) * (3 * L * B)) ^ 2 * (3 * L * B) ^ 2 := by
        gcongr
      _ = (3 * L * B) ^ 6 := by ring
  have hcancel : (3 * L * B) ^ 6 * (B ^ 8)⁻¹ =
      729 * L ^ 6 * (B⁻¹) ^ 2 := by
    field_simp [ne_of_gt hB0]
    ring
  have hBinv : B⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀' hB0]
    nlinarith
  have hBinv0 : 0 ≤ B⁻¹ := inv_nonneg.mpr hB0.le
  change ‖(((s + w) * (1 - (s + w))) ^ 2 * (sbar + w) ^ 2) *
      (afePoleNormalization t)⁻¹‖ ≤ _
  rw [norm_mul, hInvNorm]
  calc
    _ ≤ (3 * L * B) ^ 6 * (B ^ 8)⁻¹ := by gcongr
    _ = 729 * L ^ 6 * (B⁻¹) ^ 2 := hcancel
    _ ≤ 729 * L ^ 6 * 2 ^ 2 := by gcongr
    _ = 2916 * (1 + |u|) ^ 6 := by dsimp only [L]; ring

set_option maxHeartbeats 1000000 in
/-- Uniform source-line bound for one regularized equation-(84) kernel.
The constant is independent of the physical ordinate `t`.  The proof keeps
the paired real-Gamma quotient intact, so the Gaussian leaves an explicit
`exp (-50 u^2)` tail after the reciprocal ordinary Gamma factor is included. -/
theorem exists_norm_hughesYoungEquation84RegularizedContourKernel_sourceLine_le
    (CX COne : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ),
      ‖hughesYoungEquation84RegularizedContourKernel t
          ((1 : ℂ) + (u : ℂ) * I) CX COne‖ ≤
        C * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14 *
          (3 + |t| + |u|) ^ 5 := by
  obtain ⟨B, hB, hBeta⟩ :=
    exists_norm_hughesYoungEquation84RegularizedBetaKernel_sourceLine_joint_le
      CX COne
  let G : ℝ := 1 + Real.pi⁻¹ ^ 2 * Real.exp 8
  let C : ℝ := 625 * 2916 * B * G ^ 2
  have hG : 0 < G := by dsimp only [G]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t u
  let w : ℂ := (1 : ℂ) + (u : ℂ) * I
  let p : ℂ := afeCriticalPoint t + w
  let q : ℂ := afeCriticalPoint (-t) + w
  let R : ℝ := 3 + |t| + |u|
  let L : ℝ := 1 + |u|
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith [abs_nonneg t, abs_nonneg u]
  have hR3 : 3 ≤ R := by dsimp only [R]; linarith [abs_nonneg t, abs_nonneg u]
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have htpuR : |t + u| ≤ R := by
    calc
      |t + u| ≤ |t| + |u| := abs_add_le _ _
      _ ≤ R := by dsimp only [R]; linarith
  have hmtpuR : |-t + u| ≤ R := by
    calc
      |-t + u| ≤ |-t| + |u| := abs_add_le _ _
      _ ≤ R := by simp only [abs_neg]; dsimp only [R]; linarith
  have hplusFactor : 1 + |t + u| ≤ R := by
    calc
      1 + |t + u| ≤ 1 + (|t| + |u|) := by gcongr; exact abs_add_le _ _
      _ ≤ R := by dsimp only [R]; linarith
  have hminusFactor : 1 + |-t + u| ≤ R := by
    calc
      1 + |-t + u| ≤ 1 + (|-t| + |u|) := by gcongr; exact abs_add_le _ _
      _ ≤ R := by simp only [abs_neg]; dsimp only [R]; linarith
  have hGamma : ‖hughesYoungGammaRatioShift t 1 u‖ ≤
      Real.exp (16 * u ^ 2) * G ^ 2 * R ^ 2 := by
    calc
      _ ≤ Real.exp (16 * u ^ 2) *
          (1 + Real.pi⁻¹ ^ 2 * Real.exp 8) ^ 2 *
          (1 + |t + u|) * (1 + |-t + u|) :=
        norm_hughesYoungGammaRatioShift_one_le t u
      _ ≤ Real.exp (16 * u ^ 2) * G ^ 2 * R * R := by
        dsimp only [G]
        gcongr
      _ = Real.exp (16 * u ^ 2) * G ^ 2 * R ^ 2 := by ring
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith [abs_nonneg u]
  have hwNorm : ‖w‖ ≤ L := by
    calc
      ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖(u : ℂ) * I‖ := by
        dsimp only [w]
        exact norm_add_le _ _
      _ = 1 + |u| := by simp [Real.norm_eq_abs]
      _ = L := rfl
  have hAux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625 * L ^ 8 :=
    norm_hughesYoungAuxiliaryZero_le_polynomial hL1 hwNorm
  have hGauss : ‖Complex.exp (100 * w ^ 2)‖ ≤
      Real.exp (100 - 100 * u ^ 2) := by
    have hg := norm_hughesYoungGaussian_horizontal_le
      (x := (1 : ℝ)) (c := (1 : ℝ)) (H := u) (by norm_num) le_rfl
    norm_num at hg
    simpa only [w] using hg
  have hNormalizedPoly :
      ‖((p * (1 - p)) ^ 2 * q ^ 2) * (afePoleNormalization t)⁻¹‖ ≤
        2916 * L ^ 6 := by
    simpa only [p, q, w, L] using
      norm_hughesYoungEquation84NormalizedCorePolynomial_sourceLine_le t u
  have hwInv : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hwOne : 1 ≤ ‖w‖ := by
      have hre := Complex.abs_re_le_norm w
      have hwre : w.re = 1 := by simp [w]
      rw [hwre, abs_one] at hre
      exact hre
    exact (inv_le_one₀ (zero_lt_one.trans_le hwOne)).2 hwOne
  have hBetaRaw := hBeta t u
  have hBeta : ‖hughesYoungEquation84RegularizedBetaKernel t w CX COne‖ ≤
      B * Real.exp (Real.pi * |u|) * R ^ 3 := by
    dsimp only [w, R]
    convert hBetaRaw using 1
  have hExpProduct :
      Real.exp (100 - 100 * u ^ 2) * Real.exp (16 * u ^ 2) *
          Real.exp (Real.pi * |u|) ≤
        Real.exp (102 - 80 * u ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hpi : Real.pi * |u| ≤ 4 * |u| :=
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (abs_nonneg u)
    have habsSq : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg (|u| - 1)]
  have hfactor :
      hughesYoungEquation84RegularizedContourKernel t w CX COne =
        hughesYoungAuxiliaryZero w *
          (Complex.exp (100 * w ^ 2) * (p * (1 - p)) ^ 2 * q ^ 2 *
            hughesYoungGammaRatioShift t 1 u * (afePoleNormalization t)⁻¹ *
            w⁻¹) *
          hughesYoungEquation84RegularizedBetaKernel t w CX COne := by
    rw [hughesYoungEquation84RegularizedContourKernel_eq_auxiliary_mul_core,
      hughesYoungEquation84RegularizedContourKernelCore_eq_expanded]
    have hpEq : afeCriticalPoint t + w =
        ((3 / 2 : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I := by
      dsimp only [w, afeCriticalPoint]
      push_cast
      ring
    have hqEq : afeCriticalPoint (-t) + w =
        ((3 / 2 : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I := by
      dsimp only [w, afeCriticalPoint]
      push_cast
      ring
    dsimp only [p, q]
    rw [hpEq, hqEq]
    unfold hughesYoungGammaRatioShift
    dsimp only
    simp only [div_eq_mul_inv]
    ring_nf
  have hInner :
      ‖Complex.exp (100 * w ^ 2) * (p * (1 - p)) ^ 2 * q ^ 2 *
          hughesYoungGammaRatioShift t 1 u * (afePoleNormalization t)⁻¹ * w⁻¹‖ ≤
        Real.exp (100 - 100 * u ^ 2) * (2916 * L ^ 6) *
          (Real.exp (16 * u ^ 2) * G ^ 2 * R ^ 2) * 1 := by
    calc
      _ = ‖Complex.exp (100 * w ^ 2)‖ *
          ‖((p * (1 - p)) ^ 2 * q ^ 2) * (afePoleNormalization t)⁻¹‖ *
          ‖hughesYoungGammaRatioShift t 1 u‖ *
          ‖w⁻¹‖ := by simp only [norm_mul]; ring
      _ ≤ Real.exp (100 - 100 * u ^ 2) * (2916 * L ^ 6) *
          (Real.exp (16 * u ^ 2) * G ^ 2 * R ^ 2) * 1 := by
        gcongr
  rw [hfactor]
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (625 * L ^ 8) *
        ((Real.exp (100 - 100 * u ^ 2) * (2916 * L ^ 6) *
          (Real.exp (16 * u ^ 2) * G ^ 2 * R ^ 2) * 1)) *
        (B * Real.exp (Real.pi * |u|) * R ^ 3) := by
      have hFirst := mul_le_mul hAux hInner (norm_nonneg _) (by positivity)
      exact mul_le_mul hFirst hBeta (norm_nonneg _) (by positivity)
    _ = (625 * 2916 * B * G ^ 2) *
        (Real.exp (100 - 100 * u ^ 2) * Real.exp (16 * u ^ 2) *
          Real.exp (Real.pi * |u|)) * L ^ 14 * R ^ 5 := by ring
    _ ≤ (625 * 2916 * B * G ^ 2) * Real.exp (102 - 80 * u ^ 2) *
        L ^ 14 * R ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hExpProduct (by positivity))
          (pow_nonneg (zero_le_one.trans hL1) 14))
        (pow_nonneg hR0 5)
    _ = C * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14 *
        (3 + |t| + |u|) ^ 5 := by rfl

set_option maxHeartbeats 1000000 in
/-- All four equation-(84) finite-difference coefficients share a source-line
Gaussian bound whose constant is uniform in the physical ordinate. -/
theorem exists_norm_hughesYoungEquation84KernelCoefficients_sourceLine_le :
    ∃ D : ℝ, 0 < D ∧ ∀ (t u : ℝ),
      ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤
          D * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14 *
            (3 + |t| + |u|) ^ 5 ∧
      ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤
          D * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14 *
            (3 + |t| + |u|) ^ 5 ∧
      ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤
          D * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14 *
            (3 + |t| + |u|) ^ 5 ∧
      ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤
          D * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14 *
            (3 + |t| + |u|) ^ 5 := by
  obtain ⟨D₀₀, hD₀₀, h₀₀⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_sourceLine_le 0 0
  obtain ⟨D₁₀, hD₁₀, h₁₀⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_sourceLine_le 1 0
  obtain ⟨D₀₁, hD₀₁, h₀₁⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_sourceLine_le 0 1
  obtain ⟨D₁₁, hD₁₁, h₁₁⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_sourceLine_le 1 1
  let D : ℝ := D₁₁ + D₁₀ + D₀₁ + 3 * D₀₀
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro t u
  have hs := fourFiniteDifference_norm_le
    (hughesYoungEquation84RegularizedContourKernel t
      ((1 : ℂ) + (u : ℂ) * I) 0 0)
    (hughesYoungEquation84RegularizedContourKernel t
      ((1 : ℂ) + (u : ℂ) * I) 1 0)
    (hughesYoungEquation84RegularizedContourKernel t
      ((1 : ℂ) + (u : ℂ) * I) 0 1)
    (hughesYoungEquation84RegularizedContourKernel t
      ((1 : ℂ) + (u : ℂ) * I) 1 1)
    D₀₀ D₁₀ D₀₁ D₁₁
    (Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14)
      ((3 + |t| + |u|) ^ 5)
    hD₀₀ hD₁₀ hD₀₁ hD₁₁ (by positivity) (by positivity)
    (by simpa only [mul_assoc] using h₀₀ t u)
    (by simpa only [mul_assoc] using h₁₀ t u)
    (by simpa only [mul_assoc] using h₀₁ t u)
    (by simpa only [mul_assoc] using h₁₁ t u)
  simpa only [D, hughesYoungEquation84Kernel00,
    hughesYoungEquation84Kernel10, hughesYoungEquation84Kernel01,
    hughesYoungEquation84Kernel11, mul_assoc] using hs

/-- The fixed Gaussian moment left after the physical height has been
factored from the all-ordinate source-line estimate. -/
noncomputable def hughesYoungEquation84SourceLineGaussianMoment : ℝ :=
  (∫ u : ℝ, Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 19) + 1

theorem integrable_hughesYoungEquation84SourceLineGaussianMoment :
    Integrable (fun u : ℝ =>
      Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 19) :=
  integrable_exp_sub_mul_sq_mul_add_abs_pow 102 (by norm_num) 19

theorem hughesYoungEquation84SourceLineGaussianMoment_pos :
    0 < hughesYoungEquation84SourceLineGaussianMoment := by
  unfold hughesYoungEquation84SourceLineGaussianMoment
  have hnonneg : 0 ≤ ∫ u : ℝ,
      Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 19 :=
    integral_nonneg fun _ => by positivity
  linarith

theorem integral_sourceLineGaussian_le_moment :
    (∫ u : ℝ, Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 19) ≤
      hughesYoungEquation84SourceLineGaussianMoment := by
  unfold hughesYoungEquation84SourceLineGaussianMoment
  linarith

/-- The positive analytic envelope is integrable independently of the
arithmetic shift cutoff. -/
theorem integrable_hughesYoungEquation84PositiveShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) :
    Integrable (hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b) := by
  obtain ⟨K, _hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k 1 (((a : ℂ) * b)⁻¹) (c₀ := 1) (c₁ := 1)
  obtain ⟨D, _hD, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      t (c₀ := 1) (c₁ := 1) (by norm_num) (by norm_num) (by norm_num)
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b)
    (continuous_hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
  have hoRaw := hOuter u 1 (by simp)
  have ho : ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ ≤ K := by
    simpa only [hughesYoungEquation84CompletePositiveOuter,
      hughesYoungCentralShiftPower, Nat.cast_one,
      Real.log_one, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using hoRaw
  have hc := hCoeff u hu1 hut 1 (by simp)
  let E : ℝ := Real.exp (100 - 60 * u ^ 2)
  let R : ℝ := (2 + |t| + 1 + |u|) ^ 17
  have hc' :
      ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R ∧
      ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R ∧
      ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R ∧
      ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R := by
    norm_num at hc
    simpa only [E, R] using hc
  rw [norm_hughesYoungEquation84PositiveShiftTailEnvelope]
  calc
    ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ *
        (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖)
        ≤ K * (4 * (D * E * R)) := by
          gcongr
          linarith [hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2]
    _ = (4 * K * D) * Real.exp (100 - 60 * u ^ 2) *
          ((2 + |t| + 1) + |u|) ^ 17 := by
      dsimp [E, R]
      ring

/-- The negative analytic envelope is integrable independently of the
arithmetic shift cutoff. -/
theorem integrable_hughesYoungEquation84NegativeShiftTailEnvelope
    (T t : ℝ) (h k a b : ℕ) :
    Integrable (hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b) := by
  obtain ⟨K, _hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k 1 (((b : ℂ) * a)⁻¹) (c₀ := 1) (c₁ := 1)
  obtain ⟨D, _hD, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      (-t) (c₀ := 1) (c₁ := 1) (by norm_num) (by norm_num) (by norm_num)
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b)
    (continuous_hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |-t| + 1 ≤ |u| := by
    rw [abs_neg]
    exact (le_max_right 1 (|t| + 1)).trans hu
  have hoRaw := hOuter u 1 (by simp)
  have ho : ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ ≤ K := by
    simpa only [hughesYoungEquation84CompleteNegativeOuter,
      hughesYoungCentralShiftPower, Nat.cast_one,
      Real.log_one, ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using hoRaw
  have hc := hCoeff u hu1 hut 1 (by simp)
  let E : ℝ := Real.exp (100 - 60 * u ^ 2)
  let R : ℝ := (2 + |t| + 1 + |u|) ^ 17
  have hc' :
      ‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R ∧
      ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R ∧
      ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R ∧
      ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ ≤ D * E * R := by
    norm_num [abs_neg] at hc
    simpa only [E, R, abs_neg] using hc
  rw [norm_hughesYoungEquation84NegativeShiftTailEnvelope]
  calc
    ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ *
        (‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖)
        ≤ K * (4 * (D * E * R)) := by
          gcongr
          linarith [hc'.1, hc'.2.1, hc'.2.2.1, hc'.2.2.2]
    _ = (4 * K * D) * Real.exp (100 - 60 * u ^ 2) *
          ((2 + |t| + 1) + |u|) ^ 17 := by
      dsimp [E, R]
      ring

set_option maxHeartbeats 1000000 in
/-- The complete positive source-line envelope at the actual reduced
moduli has a polynomial height bound with an absolute constant. -/
theorem exists_integral_norm_hughesYoungEquation84PositiveShiftTailEnvelope_reduced_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t : ℝ) {h k : ℕ}, 0 < h → 0 < k →
      (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖) ≤
        C * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5 := by
  obtain ⟨D, hD, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_sourceLine_le
  let M : ℝ := hughesYoungEquation84SourceLineGaussianMoment
  let C : ℝ := 4 * D * M
  have hM : 0 < M := by
    simpa only [M] using hughesYoungEquation84SourceLineGaussianMoment_pos
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T t h k hh hk
  let Q : ℝ := ‖hughesYoungLocalizedStaticScalar T h k‖ *
    (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
    (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ)
  let A : ℝ := 3 + |t|
  let f : ℝ → ℝ := fun u =>
    Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 19
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hf : Integrable f := by
    simpa only [f] using integrable_hughesYoungEquation84SourceLineGaussianMoment
  have henv := (integrable_hughesYoungEquation84PositiveShiftTailEnvelope T t h k
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)).norm
  have hpoint (u : ℝ) :
      ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖ ≤
          (4 * D * Q * A ^ 5) * f u := by
    obtain ⟨h₀₀, h₁₀, h₀₁, h₁₁⟩ := hCoeff t u
    have hscale : 3 + |t| + |u| ≤ A * (1 + |u|) := by
      dsimp only [A]
      nlinarith [abs_nonneg t, abs_nonneg u]
    have hscalePow : (3 + |t| + |u|) ^ 5 ≤
        A ^ 5 * (1 + |u|) ^ 5 := by
      calc
        _ ≤ (A * (1 + |u|)) ^ 5 := by gcongr
        _ = A ^ 5 * (1 + |u|) ^ 5 := by rw [mul_pow]
    have hsum :
        ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ ≤
        4 * D * Real.exp (102 - 80 * u ^ 2) *
          (1 + |u|) ^ 14 * (A ^ 5 * (1 + |u|) ^ 5) := by
      have hbase : 0 ≤ D * Real.exp (102 - 80 * u ^ 2) *
          (1 + |u|) ^ 14 * (3 + |t| + |u|) ^ 5 := by positivity
      calc
        _ ≤ 4 * (D * Real.exp (102 - 80 * u ^ 2) *
            (1 + |u|) ^ 14 * (3 + |t| + |u|) ^ 5) := by linarith
        _ = (4 * D * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14) *
            (3 + |t| + |u|) ^ 5 := by ring
        _ ≤ (4 * D * Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 14) *
            (A ^ 5 * (1 + |u|) ^ 5) := by gcongr
        _ = 4 * (D * Real.exp (102 - 80 * u ^ 2) *
            ((1 + |u|) ^ 14 * (A ^ 5 * (1 + |u|) ^ 5))) := by ring
        _ = _ := by ring
    rw [norm_hughesYoungEquation84PositiveShiftTailEnvelope,
      norm_hughesYoungEquation84CompletePositiveOuter_reduced_eq T t hh hk u]
    dsimp only [Q, A, f]
    calc
      _ ≤ Q * (4 * D * Real.exp (102 - 80 * u ^ 2) *
          ((1 + |u|) ^ 14 * ((3 + |t|) ^ 5 * (1 + |u|) ^ 5))) :=
        mul_le_mul_of_nonneg_left (by simpa only [A, mul_assoc] using hsum) hQ
      _ = (4 * D * Q * (3 + |t|) ^ 5) *
          (Real.exp (102 - 80 * u ^ 2) * (1 + |u|) ^ 19) := by ring
  have hmajor : Integrable (fun u : ℝ => (4 * D * Q * A ^ 5) * f u) :=
    hf.const_mul (4 * D * Q * A ^ 5)
  have hint :
      (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖) ≤
        ∫ u : ℝ, (4 * D * Q * A ^ 5) * f u :=
    integral_mono_ae henv hmajor (ae_of_all _ hpoint)
  calc
    _ ≤ ∫ u : ℝ, (4 * D * Q * A ^ 5) * f u := hint
    _ = (4 * D * Q * A ^ 5) * ∫ u : ℝ, f u := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (4 * D * Q * A ^ 5) * M := by
      gcongr
      simpa only [f, M] using integral_sourceLineGaussian_le_moment
    _ = C * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5 := by
      dsimp only [C, Q, A]
      ring

/-- The negative source-line envelope obeys the same reduced-modulus bound,
by the exact coordinate swap in equation (84). -/
theorem exists_integral_norm_hughesYoungEquation84NegativeShiftTailEnvelope_reduced_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t : ℝ) {h k : ℕ}, 0 < h → 0 < k →
      (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖) ≤
        C * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5 := by
  obtain ⟨C, hC, hpositive⟩ :=
    exists_integral_norm_hughesYoungEquation84PositiveShiftTailEnvelope_reduced_le
  refine ⟨C, hC, ?_⟩
  intro T t h k hh hk
  have heq (u : ℝ) :
      ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖ =
        ‖hughesYoungEquation84PositiveShiftTailEnvelope T (-t) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖ := by
    rw [norm_hughesYoungEquation84NegativeShiftTailEnvelope,
      norm_hughesYoungEquation84PositiveShiftTailEnvelope,
      norm_hughesYoungEquation84CompleteNegativeOuter_reduced_eq T t hh hk u,
      norm_hughesYoungEquation84CompletePositiveOuter_reduced_eq T (-t) hh hk u]
  calc
    (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖) =
        ∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope T (-t) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) u‖ := by
            apply integral_congr_ae
            filter_upwards [] with u
            exact heq u
    _ ≤ C * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |-t|) ^ 5 := hpositive T (-t) hh hk
    _ = C * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5 := by rw [abs_neg]

/-- The positive equation-(84) completion tail retains its explicit
arithmetic cutoff saving after the vertical contour integral. -/
theorem norm_integral_hughesYoungEquation84PositiveContourTermShiftTail_le
    (T t : ℝ) (h k : ℕ) {a b L : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hL : 0 < L)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖∫ u : ℝ, hughesYoungEquation84PositiveContourTermShiftTail
        T t h k a b u (L : ℝ)‖ ≤
      hughesYoungEquation84ShiftTailArithmeticBound a b η (L : ℝ) *
        ∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
          T t h k a b u‖ := by
  let D := hughesYoungEquation84ShiftTailArithmeticBound a b η (L : ℝ)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hD : 0 ≤ D :=
    hughesYoungEquation84ShiftTailArithmeticBound_nonneg a b hLreal
  have htail := integrable_hughesYoungEquation84PositiveContourTermShiftTail_nat
    T t h k ha hb hab L
  have henv := integrable_hughesYoungEquation84PositiveShiftTailEnvelope
    T t h k a b
  have hdom : Integrable (fun u : ℝ =>
      D * ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b u‖) :=
    henv.norm.const_mul D
  calc
    ‖∫ u : ℝ, hughesYoungEquation84PositiveContourTermShiftTail
        T t h k a b u (L : ℝ)‖
        ≤ ∫ u : ℝ, ‖hughesYoungEquation84PositiveContourTermShiftTail
            T t h k a b u (L : ℝ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ,
        D * ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b u‖ := by
      apply integral_mono_ae htail.norm hdom
      filter_upwards [] with u
      have hs := norm_hughesYoungEquation84PositiveShiftTailSourceLine_le
        T t h k ha hb u hLreal hη hη4
      rw [hughesYoungEquation84PositiveContourTermShiftTail_eq_sourceTail
          T t h k ha hb hab u (L : ℝ) hη hη4,
        norm_hughesYoungEquation84PositiveShiftTailEnvelope]
      change _ ≤ D * _
      change _ ≤ _ at hs
      nlinarith
    _ = D * ∫ u : ℝ,
        ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b u‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := rfl

/-- The negative equation-(84) completion tail retains its explicit
arithmetic cutoff saving after the vertical contour integral. -/
theorem norm_integral_hughesYoungEquation84NegativeContourTermShiftTail_le
    (T t : ℝ) (h k : ℕ) {a b L : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hL : 0 < L)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖∫ u : ℝ, hughesYoungEquation84NegativeContourTermShiftTail
        T t h k a b u (L : ℝ)‖ ≤
      hughesYoungEquation84ShiftTailArithmeticBound b a η (L : ℝ) *
        ∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
          T t h k a b u‖ := by
  let D := hughesYoungEquation84ShiftTailArithmeticBound b a η (L : ℝ)
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hD : 0 ≤ D :=
    hughesYoungEquation84ShiftTailArithmeticBound_nonneg b a hLreal
  have htail := integrable_hughesYoungEquation84NegativeContourTermShiftTail_nat
    T t h k ha hb hab L
  have henv := integrable_hughesYoungEquation84NegativeShiftTailEnvelope
    T t h k a b
  have hdom : Integrable (fun u : ℝ =>
      D * ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b u‖) :=
    henv.norm.const_mul D
  calc
    ‖∫ u : ℝ, hughesYoungEquation84NegativeContourTermShiftTail
        T t h k a b u (L : ℝ)‖
        ≤ ∫ u : ℝ, ‖hughesYoungEquation84NegativeContourTermShiftTail
            T t h k a b u (L : ℝ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ,
        D * ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b u‖ := by
      apply integral_mono_ae htail.norm hdom
      filter_upwards [] with u
      have hs := norm_hughesYoungEquation84NegativeShiftTailSourceLine_le
        T t h k ha hb u hLreal hη hη4
      rw [hughesYoungEquation84NegativeContourTermShiftTail_eq_sourceTail
          T t h k ha hb hab u (L : ℝ) hη hη4,
        norm_hughesYoungEquation84NegativeShiftTailEnvelope]
      change _ ≤ D * _
      change _ ≤ _ at hs
      nlinarith
    _ = D * ∫ u : ℝ,
        ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b u‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := rfl

/-- Exact identification of the project's fixed-height completion error with
the two explicit, absolutely integrable shift tails. -/
theorem hughesYoungFiniteEquation84ShiftTailAtHeight_eq_integratedSourceTails
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (K : ℕ) :
    let B := hughesYoungFullDyadicBound (K + 1)
    hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b K =
      (hughesYoungHeightWeight T t : ℂ) *
        ((∫ u : ℝ,
            hughesYoungEquation84PositiveContourTermShiftTail
              T t h k a b u (a * B : ℕ)) +
          ∫ u : ℝ,
            hughesYoungEquation84NegativeContourTermShiftTail
              T t h k a b u (b * B : ℕ)) := by
  dsimp only
  let B := hughesYoungFullDyadicBound (K + 1)
  have hfinite :=
    sum_hughesYoungFiniteSignedEquation84SourceIntegral_eq_prefixIntegrals
      T t h k ha hb hab (B := B)
  have hp := integrable_hughesYoungEquation84PositiveContourTermPrefix_nat
    T t h k ha hb hab (a * B)
  have hpt := integrable_hughesYoungEquation84PositiveContourTermShiftTail_nat
    T t h k ha hb hab (a * B)
  have hn := integrable_hughesYoungEquation84NegativeContourTermPrefix_nat
    T t h k ha hb hab (b * B)
  have hnt := integrable_hughesYoungEquation84NegativeContourTermShiftTail_nat
    T t h k ha hb hab (b * B)
  have hpos :
      (∫ u : ℝ, hughesYoungEquation84CompletePositiveSourceLine T t h k a b u) =
        (∫ u : ℝ, hughesYoungEquation84PositiveContourTermPrefix
          T t h k a b u (a * B : ℕ)) +
        ∫ u : ℝ, hughesYoungEquation84PositiveContourTermShiftTail
          T t h k a b u (a * B : ℕ) := by
    calc
      _ = ∫ u : ℝ,
          hughesYoungEquation84PositiveContourTermPrefix
              T t h k a b u (a * B : ℕ) +
            hughesYoungEquation84PositiveContourTermShiftTail
              T t h k a b u (a * B : ℕ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact hughesYoungEquation84CompletePositiveSourceLine_eq_contourPrefix_add_tail
          T t h k ha hb hab u (a * B : ℕ)
            (by norm_num : (0 : ℝ) < 1 / 8)
            (by norm_num : (1 / 8 : ℝ) < 1 / 4)
      _ = _ := integral_add hp hpt
  have hneg :
      (∫ u : ℝ, hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u) =
        (∫ u : ℝ, hughesYoungEquation84NegativeContourTermPrefix
          T t h k a b u (b * B : ℕ)) +
        ∫ u : ℝ, hughesYoungEquation84NegativeContourTermShiftTail
          T t h k a b u (b * B : ℕ) := by
    calc
      _ = ∫ u : ℝ,
          hughesYoungEquation84NegativeContourTermPrefix
              T t h k a b u (b * B : ℕ) +
            hughesYoungEquation84NegativeContourTermShiftTail
              T t h k a b u (b * B : ℕ) := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact hughesYoungEquation84CompleteNegativeSourceLine_eq_contourPrefix_add_tail
          T t h k ha hb hab u (b * B : ℕ)
            (by norm_num : (0 : ℝ) < 1 / 8)
            (by norm_num : (1 / 8 : ℝ) < 1 / 4)
      _ = _ := integral_add hn hnt
  unfold hughesYoungFiniteEquation84ShiftTailAtHeight
    hughesYoungCompleteEquation84SourceAtHeight
    hughesYoungFiniteEquation84SourceAtHeight
  dsimp only
  rw [hfinite]
  rw [hpos, hneg]
  dsimp only [B]
  ring

/-- Joint continuity of the source-line static Mellin factor in the
physical and Mellin ordinates. -/
theorem continuous_uncurry_hughesYoungReducedMellinStaticComplex_sourceLine
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungReducedMellinStaticComplex T z.1 h k
        ((1 : ℂ) + (z.2 : ℂ) * I)) := by
  have hmoll : Continuous (fun z : ℝ × ℝ =>
      hughesYoungMollifierPairTerm T z.1 h k) :=
    (continuous_hughesYoungMollifierPairTerm T hh hk).comp continuous_fst
  unfold hughesYoungReducedMellinStaticComplex
  dsimp only
  change Continuous (fun z : ℝ × ℝ =>
    hughesYoungMollifierPairTerm T z.1 h k * (1 / (Real.pi : ℂ)) *
      Complex.exp ((afeCriticalPoint z.1 + (1 + (z.2 : ℂ) * I)) *
        (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ)) *
      Complex.exp ((afeCriticalPoint (-z.1) + (1 + (z.2 : ℂ) * I)) *
        (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ)))
  have hcritical : Continuous afeCriticalPoint := by
    unfold afeCriticalPoint
    fun_prop
  have hline : Continuous (fun z : ℝ × ℝ =>
      (1 : ℂ) + (z.2 : ℂ) * I) := by fun_prop
  have hcrit : Continuous (fun z : ℝ × ℝ => afeCriticalPoint z.1) :=
    hcritical.comp continuous_fst
  have hcritNeg : Continuous (fun z : ℝ × ℝ => afeCriticalPoint (-z.1)) :=
    hcritical.comp (continuous_neg.comp continuous_fst)
  have hexpLeft : Continuous (fun z : ℝ × ℝ =>
      Complex.exp ((afeCriticalPoint z.1 + (1 + (z.2 : ℂ) * I)) *
        (Real.log (hughesYoungReducedLeft h k : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp ((hcrit.add hline).mul continuous_const)
  have hexpRight : Continuous (fun z : ℝ × ℝ =>
      Complex.exp ((afeCriticalPoint (-z.1) + (1 + (z.2 : ℂ) * I)) *
        (Real.log (hughesYoungReducedRight h k : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp ((hcritNeg.add hline).mul continuous_const)
  exact (((hmoll.mul continuous_const).mul hexpLeft).mul hexpRight)

/-- Joint continuity of the pole-cancelled beta kernel on the literal
equation-(84) source line.  All Gamma and digamma arguments occurring
here have fixed positive real part. -/
theorem continuous_uncurry_hughesYoungEquation84RegularizedBetaKernel_sourceLine
    (CX COne : ℂ) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84RegularizedBetaKernel x.1
        ((1 : ℂ) + (x.2 : ℂ) * I) CX COne) := by
  rw [continuous_iff_continuousAt]
  intro x
  let wfun : ℝ × ℝ → ℂ := fun y => (1 : ℂ) + (y.2 : ℂ) * I
  let zfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint y.1 - wfun y
  let pfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint y.1 + wfun y
  let two : ℝ × ℝ → ℂ := fun y => 2 * wfun y
  have hw : Continuous wfun := by dsimp only [wfun]; fun_prop
  have hcritical : Continuous afeCriticalPoint := by
    unfold afeCriticalPoint
    fun_prop
  have hz : Continuous zfun := by
    dsimp only [zfun]
    exact (hcritical.comp continuous_fst).sub hw
  have hp : Continuous pfun := by
    dsimp only [pfun]
    exact (hcritical.comp continuous_fst).add hw
  have htwo : Continuous two := by dsimp only [two]; fun_prop
  have hzOne : 0 < (zfun x + 1).re := by
    simp [zfun, wfun, afeCriticalPoint]
  have hpPos : 0 < (pfun x).re := by
    simp [pfun, wfun, afeCriticalPoint]
    norm_num
  have htwoPos : 0 < (two x).re := by
    simp [two, wfun]
  have hReg : ContinuousAt (fun y =>
      hughesYoungRegularizedGamma (zfun y)) x :=
    (differentiableAt_hughesYoungRegularizedGamma hzOne).continuousAt.comp
      hz.continuousAt
  have hRegPsi : ContinuousAt (fun y =>
      hughesYoungRegularizedGammaDigamma (zfun y)) x :=
    (differentiableAt_hughesYoungRegularizedGammaDigamma hzOne).continuousAt.comp
      hz.continuousAt
  have hGammaTwo : ContinuousAt (fun y => Complex.Gamma (two y)) x :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos htwoPos).continuousAt.comp
      htwo.continuousAt
  have hGammaP : ContinuousAt (fun y => Complex.Gamma (pfun y)) x :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hpPos).continuousAt.comp
      hp.continuousAt
  have hGammaP0 : Complex.Gamma (pfun x) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hpPos
  have hPsiTwo : ContinuousAt (fun y => Complex.digamma (two y)) x :=
    (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one htwoPos).continuousAt.comp
      htwo.continuousAt
  have hPsiP : ContinuousAt (fun y => Complex.digamma (pfun y)) x :=
    (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hpPos).continuousAt.comp
      hp.continuousAt
  have hPolyTwo : ContinuousAt (fun y =>
      hughesYoungPolygammaSeries 1 (two y)) x :=
    (hasDerivAt_hughesYoungPolygammaSeries 1 (by norm_num) htwoPos).continuousAt.comp
      htwo.continuousAt
  have hU : ContinuousAt (fun y => -Complex.digamma (two y) + CX) x :=
    hPsiTwo.neg.add_const CX
  have hV : ContinuousAt (fun y =>
      Complex.digamma (pfun y) - Complex.digamma (two y) + COne) x :=
    (hPsiP.sub hPsiTwo).add_const COne
  have hInner : ContinuousAt (fun y =>
      hughesYoungRegularizedGammaDigamma (zfun y) *
          (Complex.digamma (pfun y) - Complex.digamma (two y) + COne) +
        hughesYoungRegularizedGamma (zfun y) *
          ((-Complex.digamma (two y) + CX) *
              (Complex.digamma (pfun y) - Complex.digamma (two y) + COne) +
            hughesYoungPolygammaSeries 1 (two y))) x :=
    (hRegPsi.mul hV).add (hReg.mul ((hU.mul hV).add hPolyTwo))
  have hAll := (hGammaTwo.div hGammaP hGammaP0).mul hInner
  unfold hughesYoungEquation84RegularizedBetaKernel
  dsimp only [zfun, pfun, two, wfun] at hAll ⊢
  exact hAll

set_option maxHeartbeats 1000000 in
/-- Joint continuity of one full pole-cancelled equation-(84) kernel on
the source line. -/
theorem continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine
    (CX COne : ℂ) :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84RegularizedContourKernel x.1
        ((1 : ℂ) + (x.2 : ℂ) * I) CX COne) := by
  rw [continuous_iff_continuousAt]
  intro x
  let wfun : ℝ × ℝ → ℂ := fun y => (1 : ℂ) + (y.2 : ℂ) * I
  let pfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint y.1 + wfun y
  let qfun : ℝ × ℝ → ℂ := fun y => afeCriticalPoint (-y.1) + wfun y
  have hw : Continuous wfun := by dsimp only [wfun]; fun_prop
  have hcritical : Continuous afeCriticalPoint := by
    unfold afeCriticalPoint
    fun_prop
  have hp : Continuous pfun := by
    dsimp only [pfun]
    exact (hcritical.comp continuous_fst).add hw
  have hq : Continuous qfun := by
    dsimp only [qfun]
    exact (hcritical.comp (continuous_neg.comp continuous_fst)).add hw
  have hpPos : 0 < (pfun x).re := by
    simp [pfun, wfun, afeCriticalPoint]
    norm_num
  have hqPos : 0 < (qfun x).re := by
    simp [qfun, wfun, afeCriticalPoint]
    norm_num
  have hGammaP : ContinuousAt (fun y => Complex.Gammaℝ (pfun y)) x :=
    (differentiableAt_GammaR_of_re_pos hpPos).continuousAt.comp hp.continuousAt
  have hGammaQ : ContinuousAt (fun y => Complex.Gammaℝ (qfun y)) x :=
    (differentiableAt_GammaR_of_re_pos hqPos).continuousAt.comp hq.continuousAt
  have hpole : Continuous (fun y : ℝ × ℝ =>
      afePoleNormalization y.1) :=
    continuous_afePoleNormalization.comp continuous_fst
  have hgammaNorm : Continuous (fun y : ℝ × ℝ =>
      afeGammaNormalization y.1) :=
    continuous_afeGammaNormalization.comp continuous_fst
  have hw0 : wfun x ≠ 0 := by
    intro hx
    have hre := congrArg Complex.re hx
    simp [wfun] at hre
  have hbeta : ContinuousAt (fun y : ℝ × ℝ =>
      hughesYoungEquation84RegularizedBetaKernel y.1 (wfun y) CX COne) x := by
    simpa only [wfun] using
      (continuous_uncurry_hughesYoungEquation84RegularizedBetaKernel_sourceLine
        CX COne).continuousAt
  have haux : ContinuousAt (fun y : ℝ × ℝ =>
      hughesYoungAuxiliaryZero (wfun y)) x :=
    differentiable_hughesYoungAuxiliaryZero.continuous.continuousAt.comp hw.continuousAt
  have hexp : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.exp (100 * wfun y ^ 2)) x :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (hw.continuousAt.pow 2))
  have hpolyP : ContinuousAt (fun y : ℝ × ℝ =>
      (pfun y * (1 - pfun y)) ^ 2) x :=
    (hp.continuousAt.mul (continuousAt_const.sub hp.continuousAt)).pow 2
  have hpolyQ : ContinuousAt (fun y : ℝ × ℝ => qfun y ^ 2) x :=
    hq.continuousAt.pow 2
  have hnum : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) x :=
    ((((hexp.mul hpolyP).mul hpolyQ).mul (hGammaP.pow 2)).mul (hGammaQ.pow 2))
  have hdivPole : ContinuousAt (fun y : ℝ × ℝ =>
      (Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) /
          afePoleNormalization y.1) x :=
    hnum.div hpole.continuousAt (afePoleNormalization_ne_zero x.1)
  have hdivW : ContinuousAt (fun y : ℝ × ℝ =>
      (Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) /
          afePoleNormalization y.1 / wfun y) x :=
    hdivPole.div hw.continuousAt hw0
  have harch : ContinuousAt (fun y : ℝ × ℝ =>
      (Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2) /
          afePoleNormalization y.1 / wfun y / afeGammaNormalization y.1) x :=
    hdivW.div hgammaNorm.continuousAt (afeGammaNormalization_ne_zero x.1)
  have hcore : ContinuousAt (fun y : ℝ × ℝ =>
      Complex.exp (100 * wfun y ^ 2) *
        (pfun y * (1 - pfun y)) ^ 2 * qfun y ^ 2 *
        Complex.Gammaℝ (pfun y) ^ 2 * Complex.Gammaℝ (qfun y) ^ 2 /
        afePoleNormalization y.1 / wfun y / afeGammaNormalization y.1 *
        hughesYoungEquation84RegularizedBetaKernel y.1 (wfun y) CX COne) x := by
    exact harch.mul hbeta
  unfold hughesYoungEquation84RegularizedContourKernel
    hughesYoungEquation84RegularizedContourKernelCore
  dsimp only [pfun, qfun, wfun] at hcore haux ⊢
  exact haux.mul hcore

theorem continuous_uncurry_hughesYoungEquation84Kernel00_sourceLine :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel00 x.1 ((1 : ℂ) + (x.2 : ℂ) * I)) := by
  simpa only [hughesYoungEquation84Kernel00] using
    continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 0

theorem continuous_uncurry_hughesYoungEquation84Kernel10_sourceLine :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel10 x.1 ((1 : ℂ) + (x.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84Kernel10 hughesYoungEquation84Kernel00
  exact
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 1 0).sub
      (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 0)

theorem continuous_uncurry_hughesYoungEquation84Kernel01_sourceLine :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel01 x.1 ((1 : ℂ) + (x.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84Kernel01 hughesYoungEquation84Kernel00
  exact
    (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 1).sub
      (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 0)

theorem continuous_uncurry_hughesYoungEquation84Kernel11_sourceLine :
    Continuous (fun x : ℝ × ℝ =>
      hughesYoungEquation84Kernel11 x.1 ((1 : ℂ) + (x.2 : ℂ) * I)) := by
  unfold hughesYoungEquation84Kernel11 hughesYoungEquation84Kernel10
    hughesYoungEquation84Kernel01 hughesYoungEquation84Kernel00
  exact (((
    continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 1 1).sub
      ((continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 1 0).sub
        (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 0))).sub
      ((continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 1).sub
        (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 0))).sub
      (continuous_uncurry_hughesYoungEquation84RegularizedContourKernel_sourceLine 0 0)

/-- Each equation-(96) source-line summand is continuous in the Mellin
ordinate; its only nonconstant factor is a complex power with positive
integer base. -/
theorem continuous_hughesYoungEquation96PositiveTerm_vertical
    (h k : ℕ) (y : ℕ+ × ℕ+) :
    Continuous (fun u : ℝ =>
      hughesYoungEquation96PositiveTerm h k 1 1
        ((2 : ℂ) + (2 * u : ℂ) * I) y) := by
  have hyOne : (((y.1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.1.property.ne'
  have hyTwo : (((y.2 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.2.property.ne'
  have hvar : Continuous (fun u : ℝ =>
      (((y.2 : ℕ) : ℂ)) ^ ((2 : ℂ) + (2 * u : ℂ) * I)) :=
    continuous_const_cpow_of_ne_zero (((y.2 : ℕ) : ℂ)) hyTwo (by fun_prop)
  unfold hughesYoungEquation96PositiveTerm
  exact continuous_const.div₀ (continuous_const.mul hvar) (fun _ =>
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hyOne))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hyTwo)))

theorem aestronglyMeasurable_hughesYoungEquation96VerticalShiftTailMoment
    (h k : ℕ) (i j : Bool) (B : ℝ) :
    AEStronglyMeasurable (fun u : ℝ =>
      hughesYoungEquation96VerticalShiftTailMoment h k i j u B) := by
  apply AEMeasurable.aestronglyMeasurable
  unfold hughesYoungEquation96VerticalShiftTailMoment
  apply AEMeasurable.tsum
  intro y
  by_cases hy : B < ((y.2 : ℕ) : ℝ)
  · simp only [hy, if_true]
    exact ((continuous_hughesYoungEquation96PositiveTerm_vertical h k y).mul
      continuous_const |>.mul continuous_const).aemeasurable
  · simp only [hy, if_false]
    exact aemeasurable_const

theorem continuous_uncurry_hughesYoungEquation84CompletePositiveOuter_sourceLine
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b : ℕ) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompletePositiveOuter T z.1 h k a b z.2) := by
  unfold hughesYoungEquation84CompletePositiveOuter
  exact continuous_const.mul
    (continuous_uncurry_hughesYoungReducedMellinStaticComplex_sourceLine T hh hk)

theorem continuous_uncurry_hughesYoungEquation84CompleteNegativeOuter_sourceLine
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (a b : ℕ) :
    Continuous (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompleteNegativeOuter T z.1 h k a b z.2) := by
  unfold hughesYoungEquation84CompleteNegativeOuter
  exact continuous_const.mul
    (continuous_uncurry_hughesYoungReducedMellinStaticComplex_sourceLine T hh hk)

/-- Joint measurability of the positive omitted source family. -/
theorem aestronglyMeasurable_uncurry_hughesYoungEquation84PositiveShiftTailSourceLine
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b : ℕ) (B : ℝ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveShiftTailSourceLine
        T z.1 h k a b z.2 B) := by
  have hOuter : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompletePositiveOuter T z.1 h k a b z.2) :=
    (continuous_uncurry_hughesYoungEquation84CompletePositiveOuter_sourceLine
      T hh hk a b).aestronglyMeasurable
  have hm (i j : Bool) : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation96VerticalShiftTailMoment a b i j z.2 B) :=
    (aestronglyMeasurable_hughesYoungEquation96VerticalShiftTailMoment
      a b i j B).comp_snd
  have h₀₀ := (hm false false).mul
    continuous_uncurry_hughesYoungEquation84Kernel00_sourceLine.aestronglyMeasurable
  have h₁₀ := (hm true false).mul
    continuous_uncurry_hughesYoungEquation84Kernel10_sourceLine.aestronglyMeasurable
  have h₀₁ := (hm false true).mul
    continuous_uncurry_hughesYoungEquation84Kernel01_sourceLine.aestronglyMeasurable
  have h₁₁ := (hm true true).mul
    continuous_uncurry_hughesYoungEquation84Kernel11_sourceLine.aestronglyMeasurable
  unfold hughesYoungEquation84PositiveShiftTailSourceLine
  exact hOuter.mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)

/-- Joint measurability of the coordinate-swapped negative omitted source
family. -/
theorem aestronglyMeasurable_uncurry_hughesYoungEquation84NegativeShiftTailSourceLine
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (a b : ℕ) (B : ℝ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84NegativeShiftTailSourceLine
        T z.1 h k a b z.2 B) := by
  have hOuter : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompleteNegativeOuter T z.1 h k a b z.2) :=
    (continuous_uncurry_hughesYoungEquation84CompleteNegativeOuter_sourceLine
      T hh hk a b).aestronglyMeasurable
  have hm (i j : Bool) : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation96VerticalShiftTailMoment b a i j z.2 B) :=
    (aestronglyMeasurable_hughesYoungEquation96VerticalShiftTailMoment
      b a i j B).comp_snd
  let negPair : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1, z.2)
  have hnegPair : Continuous negPair := by dsimp only [negPair]; fun_prop
  have h₀₀ := (hm false false).mul
    (continuous_uncurry_hughesYoungEquation84Kernel00_sourceLine.comp
      hnegPair).aestronglyMeasurable
  have h₁₀ := (hm true false).mul
    (continuous_uncurry_hughesYoungEquation84Kernel10_sourceLine.comp
      hnegPair).aestronglyMeasurable
  have h₀₁ := (hm false true).mul
    (continuous_uncurry_hughesYoungEquation84Kernel01_sourceLine.comp
      hnegPair).aestronglyMeasurable
  have h₁₁ := (hm true true).mul
    (continuous_uncurry_hughesYoungEquation84Kernel11_sourceLine.comp
      hnegPair).aestronglyMeasurable
  unfold hughesYoungEquation84NegativeShiftTailSourceLine
  dsimp only [negPair] at h₀₀ h₁₀ h₀₁ h₁₁
  exact hOuter.mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)

theorem aestronglyMeasurable_uncurry_hughesYoungEquation84PositiveContourTermShiftTail
    (T : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (B : ℝ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84PositiveContourTermShiftTail
        T z.1 h k a b z.2 B) := by
  refine (aestronglyMeasurable_uncurry_hughesYoungEquation84PositiveShiftTailSourceLine
    T hh hk a b B).congr ?_
  filter_upwards [] with z
  exact (hughesYoungEquation84PositiveContourTermShiftTail_eq_sourceTail
    T z.1 h k ha hb hab z.2 B (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).symm

theorem aestronglyMeasurable_uncurry_hughesYoungEquation84NegativeContourTermShiftTail
    (T : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (B : ℝ) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84NegativeContourTermShiftTail
        T z.1 h k a b z.2 B) := by
  refine (aestronglyMeasurable_uncurry_hughesYoungEquation84NegativeShiftTailSourceLine
    T hh hk a b B).congr ?_
  filter_upwards [] with z
  exact (hughesYoungEquation84NegativeContourTermShiftTail_eq_sourceTail
    T z.1 h k ha hb hab z.2 B (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).symm

/-- Measurability in the physical height of the exact equation-(84)
finite-to-complete shift tail.  This is kept separate from its norm
estimate because it is the hypothesis needed to integrate the exact
signed difference, rather than merely its majorant. -/
theorem aestronglyMeasurable_hughesYoungFiniteEquation84ShiftTailAtHeight
    (T : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (K : ℕ) :
    AEStronglyMeasurable (fun t : ℝ =>
      hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b K) := by
  let B := hughesYoungFullDyadicBound (K + 1)
  have hp :=
    (aestronglyMeasurable_uncurry_hughesYoungEquation84PositiveContourTermShiftTail
      T hh hk ha hb hab (a * B : ℕ)).integral_prod_right'
  have hn :=
    (aestronglyMeasurable_uncurry_hughesYoungEquation84NegativeContourTermShiftTail
      T hh hk ha hb hab (b * B : ℕ)).integral_prod_right'
  have hw : AEStronglyMeasurable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (contDiff_hughesYoungHeightWeight T).continuous).aestronglyMeasurable
  have hcombined := hw.mul (hp.add hn)
  refine hcombined.congr ?_
  filter_upwards [] with t
  symm
  simpa only [B] using
    hughesYoungFiniteEquation84ShiftTailAtHeight_eq_integratedSourceTails
      T t h k ha hb hab K

/-- Quantitative fixed-height form of the finite-to-complete equation-(84)
shift error.  The two cutoff powers are attached to the actual positive and
negative source tails before the two signs are combined. -/
theorem norm_hughesYoungFiniteEquation84ShiftTailAtHeight_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (K : ℕ)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    let B := hughesYoungFullDyadicBound (K + 1)
    ‖hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b K‖ ≤
      ‖hughesYoungHeightWeight T t‖ *
        (hughesYoungEquation84ShiftTailArithmeticBound a b η (a * B : ℕ) *
            (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
              T t h k a b u‖) +
          hughesYoungEquation84ShiftTailArithmeticBound b a η (b * B : ℕ) *
            (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
              T t h k a b u‖)) := by
  dsimp only
  let B := hughesYoungFullDyadicBound (K + 1)
  have hB : 0 < B := hughesYoungFullDyadicBound_pos (K + 1)
  have haB : 0 < a * B := Nat.mul_pos ha hB
  have hbB : 0 < b * B := Nat.mul_pos hb hB
  have hp := norm_integral_hughesYoungEquation84PositiveContourTermShiftTail_le
    T t h k ha hb hab haB hη hη4
  have hn := norm_integral_hughesYoungEquation84NegativeContourTermShiftTail_le
    T t h k ha hb hab hbB hη hη4
  rw [hughesYoungFiniteEquation84ShiftTailAtHeight_eq_integratedSourceTails
    T t h k ha hb hab K, norm_mul]
  rw [Complex.norm_real]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add hp hn)

/-- The actual terminal signed-shift cutoff used by the native finite DFI
rectangle dominates `T^30`.  This connects the analytic tail exponent to
the physical height; it is stronger than a merely abstract dyadic-depth
certificate because the conclusion names the `Nat.ceil` cutoff appearing
in `hughesYoungFiniteEquation84ShiftTailAtHeight`. -/
theorem rpow_thirty_le_hughesYoungTerminalFullDyadicBound
    {T : ℝ} (hT : 1 ≤ T) :
    T ^ (30 : ℝ) ≤
      (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) := by
  have hdepth := rpow_thirty_le_globalDepth hT
  have hratio : hughesYoungDyadicRatio ≤ 2 :=
    hughesYoungDyadicRatio_lt_two.le
  have hscale :
      hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) ≤
        2 * hughesYoungFullDyadicScale (hughesYoungGlobalDepth T + 1) := by
    rw [pow_succ, hughesYoungFullDyadicScale]
    unfold hughesYoungDyadicScale
    calc
      hughesYoungDyadicRatio ^ hughesYoungGlobalDepth T *
          hughesYoungDyadicRatio ≤
        hughesYoungDyadicRatio ^ hughesYoungGlobalDepth T * 2 :=
          mul_le_mul_of_nonneg_left hratio
            (pow_nonneg hughesYoungDyadicRatio_pos.le _)
      _ = 2 * hughesYoungDyadicRatio ^ hughesYoungGlobalDepth T := by ring
  exact hdepth.trans <| hscale.trans <|
    two_mul_hughesYoungFullDyadicScale_le_bound
      (hughesYoungGlobalDepth T + 1)

/-- Raising the terminal-cutoff comparison to the negative exponent used
by the equation-(84) tail produces the explicit `T^(-45/4)` saving. -/
theorem hughesYoungTerminalFullDyadicBound_rpow_neg_three_eighth_le
    {T : ℝ} (hT : 1 ≤ T) :
    (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ^
        (-(3 / 8 : ℝ)) ≤ T ^ (-(45 / 4 : ℝ)) := by
  let B : ℝ :=
    (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hB0 : 0 < B := by
    dsimp only [B]
    exact_mod_cast hughesYoungFullDyadicBound_pos
      (hughesYoungGlobalDepth T + 1)
  have hbase : T ^ (30 : ℝ) ≤ B := by
    simpa only [B] using rpow_thirty_le_hughesYoungTerminalFullDyadicBound hT
  have hpow : T ^ (45 / 4 : ℝ) ≤ B ^ (3 / 8 : ℝ) := by
    calc
      T ^ (45 / 4 : ℝ) = (T ^ (30 : ℝ)) ^ (3 / 8 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        congr 1
        norm_num
      _ ≤ B ^ (3 / 8 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hbase (by norm_num)
  dsimp only [B] at hB0 hpow ⊢
  rw [Real.rpow_neg hB0.le, Real.rpow_neg hT0.le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hB0 _) (Real.rpow_pos_of_pos hT0 _)).2 hpow

/-- Multiplying the terminal dyadic cutoff by either positive reduced
modulus only improves the equation-(84) negative-power saving. -/
theorem hughesYoungTerminalScaledShiftCutoff_rpow_neg_three_eighth_le
    {T : ℝ} (hT : 1 ≤ T) {a : ℕ} (ha : 0 < a) :
    ((a * hughesYoungFullDyadicBound
        (hughesYoungGlobalDepth T + 1) : ℕ) : ℝ) ^ (-(3 / 8 : ℝ)) ≤
      T ^ (-(45 / 4 : ℝ)) := by
  let B : ℕ :=
    hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1)
  have hB : 0 < B := hughesYoungFullDyadicBound_pos _
  have hBcast : (0 : ℝ) < B := by exact_mod_cast hB
  have haBcast : (0 : ℝ) < a * B := by exact_mod_cast Nat.mul_pos ha hB
  have hbase : (B : ℝ) ≤ ((a * B : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left B ha
  have hpow : (B : ℝ) ^ (3 / 8 : ℝ) ≤
      ((a * B : ℕ) : ℝ) ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow hBcast.le hbase (by norm_num)
  have hinv : ((a * B : ℕ) : ℝ) ^ (-(3 / 8 : ℝ)) ≤
      (B : ℝ) ^ (-(3 / 8 : ℝ)) := by
    simp only [Nat.cast_mul] at haBcast hbase hpow ⊢
    rw [Real.rpow_neg haBcast.le, Real.rpow_neg hBcast.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos haBcast _)
      (Real.rpow_pos_of_pos hBcast _)).2 hpow
  exact hinv.trans <| by
    simpa only [B] using
      hughesYoungTerminalFullDyadicBound_rpow_neg_three_eighth_le hT

/-- The complete arithmetic majorant for either terminal equation-(84)
tail inherits the physical-height saving.  The remaining factors are the
fixed `η = 1/8` DFI divisor constant and the two reduced-modulus powers;
no cutoff-dependent constant is hidden. -/
theorem hughesYoungEquation84TerminalShiftTailArithmeticBound_le
    {T : ℝ} (hT : 1 ≤ T) {a b : ℕ} (ha : 0 < a) :
    hughesYoungEquation84ShiftTailArithmeticBound a b (1 / 8 : ℝ)
        (a * hughesYoungFullDyadicBound
          (hughesYoungGlobalDepth T + 1) : ℕ) ≤
      (((a : ℝ) ^ (3 / 4 : ℝ) * (b : ℝ) ^ (3 / 4 : ℝ)) *
          (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((a : ℝ) ^ (1 / 8 : ℝ) * (b : ℝ) ^ (1 / 8 : ℝ))) *
        (T ^ (-(45 / 4 : ℝ)) *
          (∑' x : (ℕ+ × ℕ+) × ℕ+,
            hughesYoungPositiveTripleWeight (5 / 4 : ℝ) (3 / 8 : ℝ) x)) := by
  unfold hughesYoungEquation84ShiftTailArithmeticBound
  norm_num
  gcongr
  · exact tsum_nonneg fun x ↦
      hughesYoungPositiveTripleWeight_nonneg (5 / 4) (3 / 8) x
  · simpa only [Nat.cast_mul] using
      hughesYoungTerminalScaledShiftCutoff_rpow_neg_three_eighth_le hT ha

/-- Height-independent arithmetic coefficient left after extracting the
terminal `T^(-45/4)` shift-window saving. -/
noncomputable def hughesYoungEquation84TerminalShiftTailCoefficient
    (a b : ℕ) : ℝ :=
  (((a : ℝ) ^ (3 / 4 : ℝ) * (b : ℝ) ^ (3 / 4 : ℝ)) *
      (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
      ((a : ℝ) ^ (1 / 8 : ℝ) * (b : ℝ) ^ (1 / 8 : ℝ))) *
    (∑' x : (ℕ+ × ℕ+) × ℕ+,
      hughesYoungPositiveTripleWeight (5 / 4 : ℝ) (3 / 8 : ℝ) x)

theorem hughesYoungEquation84TerminalShiftTailCoefficient_nonneg
    (a b : ℕ) :
    0 ≤ hughesYoungEquation84TerminalShiftTailCoefficient a b := by
  unfold hughesYoungEquation84TerminalShiftTailCoefficient
  exact mul_nonneg (by positivity) <|
    tsum_nonneg fun x ↦
      hughesYoungPositiveTripleWeight_nonneg (5 / 4) (3 / 8) x

theorem hughesYoungEquation84TerminalShiftTailArithmeticBound_le_coefficient
    {T : ℝ} (hT : 1 ≤ T) {a b : ℕ} (ha : 0 < a) :
    hughesYoungEquation84ShiftTailArithmeticBound a b (1 / 8 : ℝ)
        (a * hughesYoungFullDyadicBound
          (hughesYoungGlobalDepth T + 1) : ℕ) ≤
      hughesYoungEquation84TerminalShiftTailCoefficient a b *
        T ^ (-(45 / 4 : ℝ)) := by
  have h := hughesYoungEquation84TerminalShiftTailArithmeticBound_le
    hT (a := a) (b := b) ha
  calc
    _ ≤ (((a : ℝ) ^ (3 / 4 : ℝ) * (b : ℝ) ^ (3 / 4 : ℝ)) *
          (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((a : ℝ) ^ (1 / 8 : ℝ) * (b : ℝ) ^ (1 / 8 : ℝ))) *
        (T ^ (-(45 / 4 : ℝ)) *
          (∑' x : (ℕ+ × ℕ+) × ℕ+,
            hughesYoungPositiveTripleWeight (5 / 4 : ℝ) (3 / 8 : ℝ) x)) := h
    _ = hughesYoungEquation84TerminalShiftTailCoefficient a b *
        T ^ (-(45 / 4 : ℝ)) := by
      unfold hughesYoungEquation84TerminalShiftTailCoefficient
      ring

/-- Fixed-height terminal-tail estimate with the physical-height saving
fully exposed.  This is the pointwise input for the remaining mollifier and
height integrations. -/
theorem norm_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_le
    {T : ℝ} (hT : 1 ≤ T) (t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    ‖hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b
        (hughesYoungGlobalDepth T)‖ ≤
      ‖hughesYoungHeightWeight T t‖ *
        (T ^ (-(45 / 4 : ℝ)) *
          (hughesYoungEquation84TerminalShiftTailCoefficient a b *
              (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
                T t h k a b u‖) +
            hughesYoungEquation84TerminalShiftTailCoefficient b a *
              (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
                T t h k a b u‖))) := by
  have hraw := norm_hughesYoungFiniteEquation84ShiftTailAtHeight_le
    T t h k ha hb hab (hughesYoungGlobalDepth T)
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  have hp := hughesYoungEquation84TerminalShiftTailArithmeticBound_le_coefficient
    hT (b := b) ha
  have hn := hughesYoungEquation84TerminalShiftTailArithmeticBound_le_coefficient
    hT (a := b) (b := a) hb
  have hEp : 0 ≤ ∫ u : ℝ,
      ‖hughesYoungEquation84PositiveShiftTailEnvelope T t h k a b u‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hEn : 0 ≤ ∫ u : ℝ,
      ‖hughesYoungEquation84NegativeShiftTailEnvelope T t h k a b u‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hpow : 0 ≤ T ^ (-(45 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  calc
    _ ≤ ‖hughesYoungHeightWeight T t‖ *
        (hughesYoungEquation84ShiftTailArithmeticBound a b (1 / 8 : ℝ)
              (a * hughesYoungFullDyadicBound
                (hughesYoungGlobalDepth T + 1) : ℕ) *
            (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
              T t h k a b u‖) +
          hughesYoungEquation84ShiftTailArithmeticBound b a (1 / 8 : ℝ)
              (b * hughesYoungFullDyadicBound
                (hughesYoungGlobalDepth T + 1) : ℕ) *
            (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
              T t h k a b u‖)) := by
        simpa only using hraw
    _ ≤ ‖hughesYoungHeightWeight T t‖ *
        ((hughesYoungEquation84TerminalShiftTailCoefficient a b *
              T ^ (-(45 / 4 : ℝ))) *
            (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
              T t h k a b u‖) +
          (hughesYoungEquation84TerminalShiftTailCoefficient b a *
              T ^ (-(45 / 4 : ℝ))) *
            (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
              T t h k a b u‖)) := by
        gcongr
    _ = _ := by ring

/-- At the actual reduced moduli, the terminal shift tail has only fifth
degree physical-height growth.  All arithmetic dependence is displayed
outside the universal analytic constant. -/
theorem exists_norm_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T → ∀ (t : ℝ) {h k : ℕ},
      0 < h → 0 < k →
      ‖hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungGlobalDepth T)‖ ≤
        C * ‖hughesYoungHeightWeight T t‖ * T ^ (-(45 / 4 : ℝ)) *
          ((hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
            hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5) := by
  obtain ⟨Cp, hCp, hp⟩ :=
    exists_integral_norm_hughesYoungEquation84PositiveShiftTailEnvelope_reduced_le
  obtain ⟨Cn, hCn, hn⟩ :=
    exists_integral_norm_hughesYoungEquation84NegativeShiftTailEnvelope_reduced_le
  let C : ℝ := Cp + Cn
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hT t h k hh hk
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let Q : ℝ := ‖hughesYoungLocalizedStaticScalar T h k‖ *
    (a : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ) * (3 + |t|) ^ 5
  let Apos := hughesYoungEquation84TerminalShiftTailCoefficient a b
  let Aneg := hughesYoungEquation84TerminalShiftTailCoefficient b a
  have ha : 0 < a := hughesYoungReducedLeft_pos hh
  have hb : 0 < b := hughesYoungReducedRight_pos hh hk
  have hab : a.Coprime b := hughesYoungReduced_coprime hh
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hApos : 0 ≤ Apos :=
    hughesYoungEquation84TerminalShiftTailCoefficient_nonneg a b
  have hAneg : 0 ≤ Aneg :=
    hughesYoungEquation84TerminalShiftTailCoefficient_nonneg b a
  have hEp := hp T t hh hk
  have hEn := hn T t hh hk
  have hEpQ :
      (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
          T t h k a b u‖) ≤ Cp * Q := by
    calc
      _ ≤ Cp * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5 := by simpa only [a, b] using hEp
      _ = Cp * Q := by dsimp only [Q]; ring
  have hEnQ :
      (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
          T t h k a b u‖) ≤ Cn * Q := by
    calc
      _ ≤ Cn * ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (a : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5 := by simpa only [a, b] using hEn
      _ = Cn * Q := by dsimp only [Q]; ring
  have hTnonneg : 0 ≤ T := by linarith
  have hCpC : Cp ≤ C := by dsimp only [C]; linarith
  have hCnC : Cn ≤ C := by dsimp only [C]; linarith
  have hcombine :
      Apos * (Cp * Q) + Aneg * (Cn * Q) ≤ C * (Apos + Aneg) * Q := by
    calc
      Apos * (Cp * Q) + Aneg * (Cn * Q) ≤
          Apos * (C * Q) + Aneg * (C * Q) := by
            gcongr
      _ = C * (Apos + Aneg) * Q := by ring
  have hraw := norm_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_le
    hT t h k ha hb hab
  calc
    _ ≤ ‖hughesYoungHeightWeight T t‖ *
        (T ^ (-(45 / 4 : ℝ)) *
          (Apos * (∫ u : ℝ, ‖hughesYoungEquation84PositiveShiftTailEnvelope
              T t h k a b u‖) +
            Aneg * (∫ u : ℝ, ‖hughesYoungEquation84NegativeShiftTailEnvelope
              T t h k a b u‖))) := by
      simpa only [a, b, Apos, Aneg] using hraw
    _ ≤ ‖hughesYoungHeightWeight T t‖ *
        (T ^ (-(45 / 4 : ℝ)) * (Apos * (Cp * Q) + Aneg * (Cn * Q))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hEpQ hApos)
            (mul_le_mul_of_nonneg_left hEnQ hAneg))
          (Real.rpow_nonneg hTnonneg _))
        (norm_nonneg _)
    _ ≤ ‖hughesYoungHeightWeight T t‖ *
        (T ^ (-(45 / 4 : ℝ)) * (C * (Apos + Aneg) * Q)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcombine (Real.rpow_nonneg hTnonneg _))
        (norm_nonneg _)
    _ = C * ‖hughesYoungHeightWeight T t‖ * T ^ (-(45 / 4 : ℝ)) *
        ((hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
            hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + |t|) ^ 5) := by
      dsimp only [C, Q, Apos, Aneg, a, b]
      ring

/-- The exact terminal finite-to-complete correction is Bochner integrable
in the physical height.  This is the measure-theoretic bridge needed to
move the fixed-height equation-(84) identity through the outer integral. -/
theorem integrable_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced
    {T : ℝ} (hT : 1 ≤ T) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Integrable (fun t : ℝ =>
      hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        (hughesYoungGlobalDepth T)) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced_le
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let A : ℝ := C * T ^ (-(45 / 4 : ℝ)) *
    ((hughesYoungEquation84TerminalShiftTailCoefficient a b +
      hughesYoungEquation84TerminalShiftTailCoefficient b a) *
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (a : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ) *
      (3 + 4 * T) ^ 5)
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hthreeT : 0 ≤ 3 + 4 * T := by linarith
  have hcoefficient : 0 ≤
      hughesYoungEquation84TerminalShiftTailCoefficient a b +
        hughesYoungEquation84TerminalShiftTailCoefficient b a :=
    add_nonneg
      (hughesYoungEquation84TerminalShiftTailCoefficient_nonneg a b)
      (hughesYoungEquation84TerminalShiftTailCoefficient_nonneg b a)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hmeas :=
    aestronglyMeasurable_hughesYoungFiniteEquation84ShiftTailAtHeight
      T hh hk (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) (hughesYoungReduced_coprime hh)
        (hughesYoungGlobalDepth T)
  apply hBint.mono' hmeas
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · have hzero :
        hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b
            (hughesYoungGlobalDepth T) = 0 := by
      rw [hughesYoungFiniteEquation84ShiftTailAtHeight_eq_integratedSourceTails
        T t h k (hughesYoungReducedLeft_pos hh)
          (hughesYoungReducedRight_pos hh hk) (hughesYoungReduced_coprime hh)
          (hughesYoungGlobalDepth T)]
      simp [hw]
    rw [show hughesYoungReducedLeft h k = a by rfl,
      show hughesYoungReducedRight h k = b by rfl, hzero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hA) t
  · have ht := hughesYoungHeightWeight_support hT0 hw
    have htAbs : |t| ≤ 4 * T := by
      rw [abs_of_nonneg (le_trans (by linarith [hT0]) ht.1)]
      exact ht.2
    have hthree : 0 ≤ 3 + |t| := by positivity
    have hthreeT : 3 + |t| ≤ 3 + 4 * T := by linarith
    have hpow : (3 + |t|) ^ 5 ≤ (3 + 4 * T) ^ 5 := by
      exact pow_le_pow_left₀ hthree hthreeT 5
    have hp := hpoint hT t hh hk
    have hw0 := hughesYoungHeightWeight_nonneg T t
    have hw1 := hughesYoungHeightWeight_le_one T t
    change ‖hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b
        (hughesYoungGlobalDepth T)‖ ≤ B t
    rw [show B t = A by exact Set.indicator_of_mem ht _]
    dsimp only [A, a, b] at hp ⊢
    rw [Real.norm_eq_abs, abs_of_nonneg hw0] at hp
    calc
      _ ≤ C * hughesYoungHeightWeight T t * T ^ (-(45 / 4 : ℝ)) *
          ((hughesYoungEquation84TerminalShiftTailCoefficient
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
            hughesYoungEquation84TerminalShiftTailCoefficient
                (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
            (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
            (3 + |t|) ^ 5) := hp
      _ ≤ C * 1 * T ^ (-(45 / 4 : ℝ)) *
          ((hughesYoungEquation84TerminalShiftTailCoefficient
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
            hughesYoungEquation84TerminalShiftTailCoefficient
                (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
            (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
            (3 + 4 * T) ^ 5) := by gcongr
      _ = _ := by ring

/-- Joint measurability of the complete positive equation-(84) source in
physical height and Mellin ordinate. -/
theorem aestronglyMeasurable_uncurry_hughesYoungEquation84CompletePositiveSourceLine
    (T : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompletePositiveSourceLine
        T z.1 h k a b z.2) := by
  have hOuter : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompletePositiveOuter T z.1 h k a b z.2) :=
    (continuous_uncurry_hughesYoungEquation84CompletePositiveOuter_sourceLine
      T hh hk a b).aestronglyMeasurable
  have hm (i j : Bool) : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompletePositiveMomentAt a b i j z.2) :=
    (continuous_hughesYoungEquation84CompletePositiveMomentAt i j ha hb hab
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).aestronglyMeasurable.comp_snd
  have h₀₀ := (hm false false).mul
    continuous_uncurry_hughesYoungEquation84Kernel00_sourceLine.aestronglyMeasurable
  have h₁₀ := (hm true false).mul
    continuous_uncurry_hughesYoungEquation84Kernel10_sourceLine.aestronglyMeasurable
  have h₀₁ := (hm false true).mul
    continuous_uncurry_hughesYoungEquation84Kernel01_sourceLine.aestronglyMeasurable
  have h₁₁ := (hm true true).mul
    continuous_uncurry_hughesYoungEquation84Kernel11_sourceLine.aestronglyMeasurable
  refine (hOuter.mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)).congr ?_
  filter_upwards [] with z
  exact (hughesYoungEquation84CompletePositiveSourceLine_eq_fourMoments
    T z.1 h k ha hb hab z.2 (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).symm

/-- Joint measurability of the complete negative equation-(84) source. -/
theorem aestronglyMeasurable_uncurry_hughesYoungEquation84CompleteNegativeSourceLine
    (T : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompleteNegativeSourceLine
        T z.1 h k a b z.2) := by
  have hOuter : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompleteNegativeOuter T z.1 h k a b z.2) :=
    (continuous_uncurry_hughesYoungEquation84CompleteNegativeOuter_sourceLine
      T hh hk a b).aestronglyMeasurable
  have hm (i j : Bool) : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      hughesYoungEquation84CompletePositiveMomentAt b a i j z.2) :=
    (continuous_hughesYoungEquation84CompletePositiveMomentAt i j hb ha hab.symm
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).aestronglyMeasurable.comp_snd
  let negPair : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1, z.2)
  have hnegPair : Continuous negPair := by dsimp only [negPair]; fun_prop
  have h₀₀ := (hm false false).mul
    (continuous_uncurry_hughesYoungEquation84Kernel00_sourceLine.comp
      hnegPair).aestronglyMeasurable
  have h₁₀ := (hm true false).mul
    (continuous_uncurry_hughesYoungEquation84Kernel10_sourceLine.comp
      hnegPair).aestronglyMeasurable
  have h₀₁ := (hm false true).mul
    (continuous_uncurry_hughesYoungEquation84Kernel01_sourceLine.comp
      hnegPair).aestronglyMeasurable
  have h₁₁ := (hm true true).mul
    (continuous_uncurry_hughesYoungEquation84Kernel11_sourceLine.comp
      hnegPair).aestronglyMeasurable
  refine (hOuter.mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)).congr ?_
  filter_upwards [] with z
  exact (hughesYoungEquation84CompleteNegativeSourceLine_eq_fourMoments
    T z.1 h k ha hb hab z.2 (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)).symm

/-- Measurability of the complete source after the two Mellin integrals
have been combined at a fixed physical height. -/
theorem aestronglyMeasurable_hughesYoungCompleteEquation84SourceAtHeight
    (T : ℝ) {h k a b : ℕ} (hh : 0 < h) (hk : 0 < k)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    AEStronglyMeasurable (fun t : ℝ =>
      hughesYoungCompleteEquation84SourceAtHeight T t h k a b) := by
  have hp :=
    (aestronglyMeasurable_uncurry_hughesYoungEquation84CompletePositiveSourceLine
      T hh hk ha hb hab).integral_prod_right'
  have hn :=
    (aestronglyMeasurable_uncurry_hughesYoungEquation84CompleteNegativeSourceLine
      T hh hk ha hb hab).integral_prod_right'
  have hw : AEStronglyMeasurable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (contDiff_hughesYoungHeightWeight T).continuous).aestronglyMeasurable
  exact hw.mul (hp.add hn)

theorem aestronglyMeasurable_hughesYoungCompleteShiftedCentralAtHeight_reduced
    (T : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    AEStronglyMeasurable (fun t : ℝ =>
      hughesYoungCompleteShiftedCentralAtHeight T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)) := by
  refine (aestronglyMeasurable_hughesYoungCompleteEquation84SourceAtHeight
    T hh hk (hughesYoungReducedLeft_pos hh)
      (hughesYoungReducedRight_pos hh hk) (hughesYoungReduced_coprime hh)).congr ?_
  filter_upwards [] with t
  exact hughesYoungCompleteEquation84SourceAtHeight_eq_shifted
    T t (hughesYoungReducedLeft_pos hh)
      (hughesYoungReducedRight_pos hh hk) (hughesYoungReduced_coprime hh)

/-- The complete, cancellation-preserving central source is integrable in
physical height at the reduced moduli used by the mollifier expansion. -/
theorem integrable_hughesYoungCompleteShiftedCentralAtHeight_reduced
    {T : ℝ} (hT : 1 ≤ T) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Integrable (fun t : ℝ =>
      hughesYoungCompleteShiftedCentralAtHeight T t h k
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)) := by
  obtain ⟨C, A, hC, hA, hpoint⟩ :=
    exists_norm_hughesYoungCompleteShiftedCentralAtHeight_le
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 8)
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let D : ℝ :=
    2 * A * ‖hughesYoungLocalizedStaticScalar T h k‖ *
      ((a : ℝ) ^ ((1 / 8 : ℝ) - 1 / 2) *
        (b : ℝ) ^ ((1 / 8 : ℝ) - 1 / 2)) *
      (((a : ℝ) ^ ((1 / 8 : ℝ) / 4) * (a : ℝ) ^ (1 / 8 : ℝ)) *
        ((b : ℝ) ^ ((1 / 8 : ℝ) / 4) * (b : ℝ) ^ (1 / 8 : ℝ))) *
      (((1 / 8 : ℝ))⁻¹ ^ 5 * T ^ (4 * C * (1 / 8 : ℝ)))
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => D)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hmeas :=
    aestronglyMeasurable_hughesYoungCompleteShiftedCentralAtHeight_reduced
      T hh hk
  apply hBint.mono' hmeas
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · have hzero : hughesYoungCompleteShiftedCentralAtHeight T t h k a b = 0 := by
      unfold hughesYoungCompleteShiftedCentralAtHeight
      simp [hw]
    rw [show hughesYoungReducedLeft h k = a by rfl,
      show hughesYoungReducedRight h k = b by rfl, hzero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hD) t
  · have ht := hughesYoungHeightWeight_support hT0 hw
    have hp := hpoint T t hT ht hh hk
    change ‖hughesYoungCompleteShiftedCentralAtHeight T t h k a b‖ ≤ B t
    rw [show B t = D by exact Set.indicator_of_mem ht _]
    simpa only [D, a, b] using hp

/-- The globally defined finite-to-complete correction is exactly the
finite mollifier sum of the integrable pointwise equation-(84) shift tail.
No nonintegrable-default convention is used in this identity. -/
theorem hughesYoungFiniteEquation84IntegratedShiftTail_eq_sum_integral
    {T : ℝ} (hT : 1 ≤ T) :
    hughesYoungFiniteEquation84IntegratedShiftTail T (hughesYoungGlobalDepth T) =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∫ t : ℝ,
            hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungGlobalDepth T) := by
  classical
  unfold hughesYoungFiniteEquation84IntegratedShiftTail
    hughesYoungCompleteShiftedIntegratedCentral
    hughesYoungFiniteEquation84IntegratedSource
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hhmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hkmem
  have hh : 0 < h := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hkmem).1
  have hcomplete :=
    integrable_hughesYoungCompleteShiftedCentralAtHeight_reduced hT hh hk
  have htail :=
    integrable_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced
      hT hh hk
  have hsub := integral_sub hcomplete htail
  have hfiniteIntegral :
      (∫ t : ℝ, hughesYoungFiniteEquation84SourceAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungGlobalDepth T)) =
        (∫ t : ℝ, hughesYoungCompleteShiftedCentralAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)) -
        ∫ t : ℝ, hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungGlobalDepth T) := by
    calc
      _ = ∫ t : ℝ,
          (hughesYoungCompleteShiftedCentralAtHeight T t h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) -
            hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              (hughesYoungGlobalDepth T)) := by
            apply integral_congr_ae
            filter_upwards [] with t
            rw [hughesYoungFiniteEquation84SourceAtHeight_eq_complete_sub_shiftTail,
              hughesYoungCompleteEquation84SourceAtHeight_eq_shifted
                T t (hughesYoungReducedLeft_pos hh)
                  (hughesYoungReducedRight_pos hh hk)
                  (hughesYoungReduced_coprime hh)]
      _ = _ := hsub
  rw [hfiniteIntegral]
  ring

/-- Physical-height integration of one reduced mollifier-pair shift tail.
The factor `15*T/4` is exactly the length of the cutoff support. -/
theorem exists_norm_integral_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T → ∀ {h k : ℕ},
      0 < h → 0 < k →
      ‖∫ t : ℝ,
        hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ)) *
          ((hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
            hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
          (3 + 4 * T) ^ 5) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_norm_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced_le
  refine ⟨C, hC, ?_⟩
  intro T hT h k hh hk
  let a := hughesYoungReducedLeft h k
  let b := hughesYoungReducedRight h k
  let D : ℝ := C * T ^ (-(45 / 4 : ℝ)) *
    ((hughesYoungEquation84TerminalShiftTailCoefficient a b +
      hughesYoungEquation84TerminalShiftTailCoefficient b a) *
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (a : ℝ) ^ (1 / 2 : ℝ) * (b : ℝ) ^ (1 / 2 : ℝ) *
      (3 + 4 * T) ^ 5)
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => D)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hthreeT : 0 ≤ 3 + 4 * T := by linarith
  have hcoefficient : 0 ≤
      hughesYoungEquation84TerminalShiftTailCoefficient a b +
        hughesYoungEquation84TerminalShiftTailCoefficient b a :=
    add_nonneg
      (hughesYoungEquation84TerminalShiftTailCoefficient_nonneg a b)
      (hughesYoungEquation84TerminalShiftTailCoefficient_nonneg b a)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) =
        ∫ _t in Set.Icc (T / 4) (4 * T), D by
      exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    dsimp only [D, a, b]
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hzero :
          hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b
              (hughesYoungGlobalDepth T) = 0 := by
        rw [hughesYoungFiniteEquation84ShiftTailAtHeight_eq_integratedSourceTails
          T t h k (hughesYoungReducedLeft_pos hh)
            (hughesYoungReducedRight_pos hh hk) (hughesYoungReduced_coprime hh)
            (hughesYoungGlobalDepth T)]
        simp [hw]
      rw [show hughesYoungReducedLeft h k = a by rfl,
        show hughesYoungReducedRight h k = b by rfl, hzero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hD) t
    · have ht := hughesYoungHeightWeight_support hT0 hw
      have htAbs : |t| ≤ 4 * T := by
        rw [abs_of_nonneg (le_trans (by linarith [hT0]) ht.1)]
        exact ht.2
      have hpow : (3 + |t|) ^ 5 ≤ (3 + 4 * T) ^ 5 := by
        exact pow_le_pow_left₀ (by positivity) (by linarith) 5
      have hp := hpoint hT t hh hk
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      change ‖hughesYoungFiniteEquation84ShiftTailAtHeight T t h k a b
          (hughesYoungGlobalDepth T)‖ ≤ B t
      rw [show B t = D by exact Set.indicator_of_mem ht _]
      dsimp only [D, a, b] at hp ⊢
      rw [Real.norm_eq_abs, abs_of_nonneg hw0] at hp
      calc
        _ ≤ C * hughesYoungHeightWeight T t * T ^ (-(45 / 4 : ℝ)) *
            ((hughesYoungEquation84TerminalShiftTailCoefficient
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
              hughesYoungEquation84TerminalShiftTailCoefficient
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
              ‖hughesYoungLocalizedStaticScalar T h k‖ *
              (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
              (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
              (3 + |t|) ^ 5) := hp
        _ ≤ C * 1 * T ^ (-(45 / 4 : ℝ)) *
            ((hughesYoungEquation84TerminalShiftTailCoefficient
                  (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
              hughesYoungEquation84TerminalShiftTailCoefficient
                  (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
              ‖hughesYoungLocalizedStaticScalar T h k‖ *
              (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
              (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
              (3 + 4 * T) ^ 5) := by gcongr
        _ = _ := by ring

/-- The exact arithmetic mass occurring after the physical-height tail
estimate and before the finite mollifier summation. -/
noncomputable def hughesYoungTerminalShiftTailArithmeticMass (T : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      (hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
        hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
      (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ)

theorem hughesYoungTerminalShiftTailArithmeticMass_nonneg (T : ℝ) :
    0 ≤ hughesYoungTerminalShiftTailArithmeticMass T := by
  unfold hughesYoungTerminalShiftTailArithmeticMass
  apply Finset.sum_nonneg
  intro h _hh
  apply Finset.sum_nonneg
  intro k _hk
  have hc : 0 ≤
      hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
        hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k) :=
    add_nonneg
      (hughesYoungEquation84TerminalShiftTailCoefficient_nonneg _ _)
      (hughesYoungEquation84TerminalShiftTailCoefficient_nonneg _ _)
  positivity

/-- The global completion error is reduced to its explicit arithmetic
mass, with all analytic decay and support length exposed. -/
theorem exists_norm_hughesYoungFiniteEquation84IntegratedShiftTail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T →
      ‖hughesYoungFiniteEquation84IntegratedShiftTail
          T (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ)) *
          (hughesYoungTerminalShiftTailArithmeticMass T * (3 + 4 * T) ^ 5) := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_norm_integral_hughesYoungFiniteEquation84TerminalShiftTailAtHeight_reduced_le
  refine ⟨C, hC, ?_⟩
  intro T hT
  rw [hughesYoungFiniteEquation84IntegratedShiftTail_eq_sum_integral hT]
  calc
    ‖∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          ∫ t : ℝ, hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungGlobalDepth T)‖ ≤
      ∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          ‖∫ t : ℝ, hughesYoungFiniteEquation84ShiftTailAtHeight T t h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungGlobalDepth T)‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
          (norm_sum_le _ _))
    _ ≤ ∑ h ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
        ∑ k ∈ Finset.Icc 1 (detectorCutoff T ^ 2),
          (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ)) *
            ((hughesYoungEquation84TerminalShiftTailCoefficient
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
              hughesYoungEquation84TerminalShiftTailCoefficient
                (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
            (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) *
            (3 + 4 * T) ^ 5) := by
          apply Finset.sum_le_sum
          intro h hhmem
          apply Finset.sum_le_sum
          intro k hkmem
          exact hpair hT
            (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hhmem).1)
            (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hkmem).1)
    _ = (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ)) *
          (hughesYoungTerminalShiftTailArithmeticMass T * (3 + 4 * T) ^ 5) := by
        unfold hughesYoungTerminalShiftTailArithmeticMass
        let S := Finset.Icc 1 (detectorCutoff T ^ 2)
        let P : ℝ := (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ))
        let W : ℝ := (3 + 4 * T) ^ 5
        let q : ℕ → ℕ → ℝ := fun h k =>
          (hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
            hughesYoungEquation84TerminalShiftTailCoefficient
              (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
          ‖hughesYoungLocalizedStaticScalar T h k‖ *
          (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
          (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ)
        change (∑ h ∈ S, ∑ k ∈ S, P * (q h k * W)) =
          P * ((∑ h ∈ S, ∑ k ∈ S, q h k) * W)
        calc
          (∑ h ∈ S, ∑ k ∈ S, P * (q h k * W)) =
              ∑ h ∈ S, P * ((∑ k ∈ S, q h k) * W) := by
                apply Finset.sum_congr rfl
                intro h _
                rw [← Finset.mul_sum, ← Finset.sum_mul]
          _ = P * ((∑ h ∈ S, ∑ k ∈ S, q h k) * W) := by
                rw [← Finset.mul_sum, ← Finset.sum_mul]

/-- Universal arithmetic constant in the terminal equation-(84) tail. -/
noncomputable def hughesYoungTerminalShiftTailUniversalConstant : ℝ :=
  2 * (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    (∑' x : (ℕ+ × ℕ+) × ℕ+,
      hughesYoungPositiveTripleWeight (5 / 4 : ℝ) (3 / 8 : ℝ) x)

theorem hughesYoungTerminalShiftTailUniversalConstant_nonneg :
    0 ≤ hughesYoungTerminalShiftTailUniversalConstant := by
  unfold hughesYoungTerminalShiftTailUniversalConstant
  exact mul_nonneg (by positivity) <|
    tsum_nonneg fun x =>
      hughesYoungPositiveTripleWeight_nonneg (5 / 4) (3 / 8) x

/-- Crude but sufficient polynomial control of the terminal arithmetic
mass.  The exponent ten counts the four equation-(84) modulus powers, the
two square-root factors, two mollifier coefficients, and the two finite
index counts. -/
theorem hughesYoungTerminalShiftTailArithmeticMass_le_cutoff_twenty
    (T : ℝ) :
    hughesYoungTerminalShiftTailArithmeticMass T ≤
      hughesYoungTerminalShiftTailUniversalConstant *
        ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 10) := by
  classical
  let L : ℕ := (detectorCutoff T) ^ 2
  let S := Finset.Icc 1 L
  let Z : ℝ := ∑' x : (ℕ+ × ℕ+) × ℕ+,
    hughesYoungPositiveTripleWeight (5 / 4 : ℝ) (3 / 8 : ℝ) x
  have hZ : 0 ≤ Z := by
    dsimp only [Z]
    exact tsum_nonneg fun x =>
      hughesYoungPositiveTripleWeight_nonneg (5 / 4) (3 / 8) x
  have hterm : ∀ h ∈ S, ∀ k ∈ S,
      (hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
        hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
      (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ) ≤
        hughesYoungTerminalShiftTailUniversalConstant * (L : ℝ) ^ 8 := by
    intro h hhmem k hkmem
    have hhI := Finset.mem_Icc.mp hhmem
    have hkI := Finset.mem_Icc.mp hkmem
    have hh : 0 < h := Nat.zero_lt_of_lt hhI.1
    have hk : 0 < k := Nat.zero_lt_of_lt hkI.1
    let a := hughesYoungReducedLeft h k
    let b := hughesYoungReducedRight h k
    have ha : 0 < a := hughesYoungReducedLeft_pos hh
    have hb : 0 < b := hughesYoungReducedRight_pos hh hk
    have haL : a ≤ L :=
      (Nat.div_le_self h (Nat.gcd h k)).trans hhI.2
    have hbL : b ≤ L :=
      (Nat.div_le_self k (Nat.gcd h k)).trans hkI.2
    have hLoneNat : 1 ≤ L := by omega
    have hLone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLoneNat
    have hrpow (x : ℕ) (hx : 0 < x) (hxL : x ≤ L)
        (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
        (x : ℝ) ^ e ≤ (L : ℝ) := by
      have hxR : (0 : ℝ) ≤ x := by positivity
      have hxLR : (x : ℝ) ≤ (L : ℝ) := by exact_mod_cast hxL
      calc
        (x : ℝ) ^ e ≤ (L : ℝ) ^ e := Real.rpow_le_rpow hxR hxLR he0
        _ ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLone he1
        _ = (L : ℝ) := Real.rpow_one _
    have ha34 := hrpow a ha haL (3 / 4 : ℝ) (by norm_num) (by norm_num)
    have hb34 := hrpow b hb hbL (3 / 4 : ℝ) (by norm_num) (by norm_num)
    have ha18 := hrpow a ha haL (1 / 8 : ℝ) (by norm_num) (by norm_num)
    have hb18 := hrpow b hb hbL (1 / 8 : ℝ) (by norm_num) (by norm_num)
    have ha12 := hrpow a ha haL (1 / 2 : ℝ) (by norm_num) (by norm_num)
    have hb12 := hrpow b hb hbL (1 / 2 : ℝ) (by norm_num) (by norm_num)
    have hcoeffab : hughesYoungEquation84TerminalShiftTailCoefficient a b ≤
        (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z * (L : ℝ) ^ 4 := by
      unfold hughesYoungEquation84TerminalShiftTailCoefficient
      dsimp only [Z]
      calc
        _ ≤ (((L : ℝ) * (L : ℝ)) *
              (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
              ((L : ℝ) * (L : ℝ))) * Z := by gcongr
        _ = (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z *
              (L : ℝ) ^ 4 := by ring
    have hcoeffba : hughesYoungEquation84TerminalShiftTailCoefficient b a ≤
        (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z * (L : ℝ) ^ 4 := by
      unfold hughesYoungEquation84TerminalShiftTailCoefficient
      dsimp only [Z]
      calc
        _ ≤ (((L : ℝ) * (L : ℝ)) *
              (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
              ((L : ℝ) * (L : ℝ))) * Z := by gcongr
        _ = (49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z *
              (L : ℝ) ^ 4 := by ring
    have hcoeffh : ‖shortMobiusSquareCoeff T h‖ ≤ (L : ℝ) :=
      (norm_shortMobiusSquareCoeff_le_divisors T hh).trans <| by
        exact_mod_cast (Nat.card_divisors_le_self h).trans hhI.2
    have hcoeffk : ‖shortMobiusSquareCoeff T k‖ ≤ (L : ℝ) :=
      (norm_shortMobiusSquareCoeff_le_divisors T hk).trans <| by
        exact_mod_cast (Nat.card_divisors_le_self k).trans hkI.2
    have hstatic : ‖hughesYoungLocalizedStaticScalar T h k‖ ≤
        (L : ℝ) * (L : ℝ) :=
      (norm_hughesYoungLocalizedStaticScalar_le_coefficients hh hk).trans
        (mul_le_mul hcoeffh hcoeffk (norm_nonneg _) (by positivity))
    have hcoeffsum :
        hughesYoungEquation84TerminalShiftTailCoefficient a b +
            hughesYoungEquation84TerminalShiftTailCoefficient b a ≤
          2 * ((49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z *
            (L : ℝ) ^ 4) := by
      calc
        _ ≤ ((49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z *
              (L : ℝ) ^ 4) +
            ((49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z *
              (L : ℝ) ^ 4) := add_le_add hcoeffab hcoeffba
        _ = _ := by ring
    dsimp only [a, b] at hcoeffab hcoeffba ha12 hb12 ⊢
    calc
      _ ≤ (2 * ((49 + 2 * |Real.eulerMascheroniConstant|) ^ 2 * Z *
              (L : ℝ) ^ 4)) *
            ((L : ℝ) * (L : ℝ)) * (L : ℝ) * (L : ℝ) := by
          dsimp only [a, b] at hcoeffsum
          gcongr
      _ = hughesYoungTerminalShiftTailUniversalConstant * (L : ℝ) ^ 8 := by
        unfold hughesYoungTerminalShiftTailUniversalConstant
        dsimp only [Z]
        ring
  unfold hughesYoungTerminalShiftTailArithmeticMass
  change (∑ h ∈ S, ∑ k ∈ S, _) ≤ _
  calc
    (∑ h ∈ S, ∑ k ∈ S,
      (hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) +
        hughesYoungEquation84TerminalShiftTailCoefficient
          (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)) *
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (hughesYoungReducedLeft h k : ℝ) ^ (1 / 2 : ℝ) *
      (hughesYoungReducedRight h k : ℝ) ^ (1 / 2 : ℝ)) ≤
        ∑ _h ∈ S, ∑ _k ∈ S,
          hughesYoungTerminalShiftTailUniversalConstant * (L : ℝ) ^ 8 := by
            exact Finset.sum_le_sum fun h hhmem =>
              Finset.sum_le_sum fun k hkmem => hterm h hhmem k hkmem
    _ = (S.card : ℝ) * (S.card : ℝ) *
        (hughesYoungTerminalShiftTailUniversalConstant * (L : ℝ) ^ 8) := by
          simp
          ring
    _ ≤ (L : ℝ) * (L : ℝ) *
        (hughesYoungTerminalShiftTailUniversalConstant * (L : ℝ) ^ 8) := by
          have hcardNat : S.card ≤ L := by simp [S]
          have hcard : (S.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hcardNat
          have hsquare : (S.card : ℝ) * (S.card : ℝ) ≤
              (L : ℝ) * (L : ℝ) :=
            mul_le_mul hcard hcard (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hsquare <| mul_nonneg
            hughesYoungTerminalShiftTailUniversalConstant_nonneg (by positivity)
    _ = hughesYoungTerminalShiftTailUniversalConstant * (L : ℝ) ^ 10 := by ring
    _ = hughesYoungTerminalShiftTailUniversalConstant *
        ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 10) := by rfl

theorem eventually_hughesYoungTerminalShiftTailArithmeticMass_le :
    ∀ᶠ T : ℝ in atTop,
      hughesYoungTerminalShiftTailArithmeticMass T ≤
        hughesYoungTerminalShiftTailUniversalConstant * T ^ (5 / 11 : ℝ) := by
  filter_upwards [eventually_detectorCutoff_sq_le_rpow,
      eventually_ge_atTop (1 : ℝ)] with T hcut hT
  have hT0 : 0 ≤ T := by linarith
  have hpow : ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 10) ≤
      (T ^ (1 / 22 : ℝ)) ^ 10 :=
    by simpa only [Nat.cast_pow] using
      (pow_le_pow_left₀ (by positivity) hcut 10)
  have hrewrite : (T ^ (1 / 22 : ℝ)) ^ 10 = T ^ (5 / 11 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
    congr 1
    norm_num
  calc
    hughesYoungTerminalShiftTailArithmeticMass T ≤
        hughesYoungTerminalShiftTailUniversalConstant *
          ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 10) :=
      hughesYoungTerminalShiftTailArithmeticMass_le_cutoff_twenty T
    _ ≤ hughesYoungTerminalShiftTailUniversalConstant *
        (T ^ (1 / 22 : ℝ)) ^ 10 :=
      mul_le_mul_of_nonneg_left hpow
        hughesYoungTerminalShiftTailUniversalConstant_nonneg
    _ = _ := by rw [hrewrite]

/-- The exact finite-to-complete shift-window correction is negligible at
the native Hughes--Young scale. -/
theorem hughesYoungFiniteEquation84IntegratedShiftTail_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungFiniteEquation84IntegratedShiftTail
        T (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ :=
    exists_norm_hughesYoungFiniteEquation84IntegratedShiftTail_le
  let A : ℝ := (15 / 4 : ℝ) * C *
    hughesYoungTerminalShiftTailUniversalConstant * 7 ^ 5
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC.le)
        hughesYoungTerminalShiftTailUniversalConstant_nonneg)
      (by positivity)
  apply IsBigO.of_bound A
  filter_upwards [eventually_hughesYoungTerminalShiftTailArithmeticMass_le,
      eventually_ge_atTop (1 : ℝ)] with T hmass hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hpolyBase : 3 + 4 * T ≤ 7 * T := by linarith
  have hpoly : (3 + 4 * T) ^ 5 ≤ (7 * T) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hpolyBase 5
  have hmassR : 0 ≤ hughesYoungTerminalShiftTailUniversalConstant *
      T ^ (5 / 11 : ℝ) :=
    mul_nonneg hughesYoungTerminalShiftTailUniversalConstant_nonneg
      (Real.rpow_nonneg hT0.le _)
  have hpower :
      T * T ^ (-(45 / 4 : ℝ)) * T ^ (5 / 11 : ℝ) * T ^ (5 : ℝ) =
        T ^ (-(211 / 44 : ℝ)) := by
    calc
      _ = T ^ (1 : ℝ) * T ^ (-(45 / 4 : ℝ)) *
          T ^ (5 / 11 : ℝ) * T ^ (5 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((1 : ℝ) + (-(45 / 4 : ℝ)) + (5 / 11 : ℝ) + 5) := by
        rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
      _ = _ := by congr 1; norm_num
  have hraw := htail hT
  have hbound :
      ‖hughesYoungFiniteEquation84IntegratedShiftTail
          T (hughesYoungGlobalDepth T)‖ ≤
        A * T ^ (-(211 / 44 : ℝ)) := by
    calc
      _ ≤ (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ)) *
          (hughesYoungTerminalShiftTailArithmeticMass T *
            (3 + 4 * T) ^ 5) := hraw
      _ ≤ (15 * T / 4) * C * T ^ (-(45 / 4 : ℝ)) *
          ((hughesYoungTerminalShiftTailUniversalConstant *
              T ^ (5 / 11 : ℝ)) * (7 * T) ^ 5) := by gcongr
      _ = A *
          (T * T ^ (-(45 / 4 : ℝ)) * T ^ (5 / 11 : ℝ) * T ^ (5 : ℝ)) := by
            dsimp only [A]
            rw [mul_pow]
            norm_num
            ring
      _ = A * T ^ (-(211 / 44 : ℝ)) := by rw [hpower]
  have hpow : T ^ (-(211 / 44 : ℝ)) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungFiniteEquation84IntegratedShiftTail
        T (hughesYoungGlobalDepth T))), htarget]
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow hA)
end RiemannZeta.GuthMaynard
