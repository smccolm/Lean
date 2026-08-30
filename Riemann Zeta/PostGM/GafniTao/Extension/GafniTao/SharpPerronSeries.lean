import GafniTao.SharpPerronKernel

/-!
# Passing the sharp Perron integral through `-ζ'/ζ`

On a fixed finite vertical segment with real part greater than one, absolute
convergence of the von Mangoldt Dirichlet series supplies a summable majorant.
This file performs the resulting interval-integral interchange.  The proof is
independent of the later contour shift and zero estimates.
-/

open scoped BigOperators Interval
open MeasureTheory

namespace GafniTao

private noncomputable def sharpPerronSeriesTerm
    (c x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((c : ℂ) + (t : ℂ) * Complex.I) n *
    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
      ((c : ℂ) + (t : ℂ) * Complex.I)

private theorem norm_LSeriesTerm_vertical_eq
    {c t : ℝ} (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((c : ℂ) + (t : ℂ) * Complex.I) n‖ =
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (c : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [norm_div]
    congr 1
    change
      ‖((n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖((n : ℝ) : ℂ) ^ (c : ℂ)‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp

private theorem norm_sharpPerronSeriesTerm_le
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖sharpPerronSeriesTerm c x n t‖ ≤
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (c : ℂ) n‖ * (x ^ c / c) := by
  have hsNorm : c ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * Complex.I)
    simpa [abs_of_pos hc] using h
  have hxNorm :
      ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ c := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx
      ((c : ℂ) + (t : ℂ) * Complex.I)
  have hsPos : 0 < ‖(c : ℂ) + (t : ℂ) * Complex.I‖ :=
    hc.trans_le hsNorm
  rw [sharpPerronSeriesTerm, norm_div, norm_mul,
    norm_LSeriesTerm_vertical_eq n, hxNorm]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le c)) hc hsNorm

private theorem aestronglyMeasurable_sharpPerronSeriesTerm
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) (T : ℝ) :
    AEStronglyMeasurable (sharpPerronSeriesTerm c x n)
      (volume.restrict (Set.uIoc (-T) T)) := by
  have hs : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hs_ne : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, Complex.zero_re] at hre
    linarith
  have hxpow : Continuous
      (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    exact Continuous.cpow continuous_const hs
      (fun _ => Complex.ofReal_mem_slitPlane.mpr hx)
  by_cases hn : n = 0
  · subst n
    have hzero : sharpPerronSeriesTerm c x 0 = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [sharpPerronSeriesTerm, LSeries.term_def]
      simp
    rw [hzero]
    exact aestronglyMeasurable_const
  · have hnpow : Continuous
        (fun t : ℝ => (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
      exact Continuous.cpow continuous_const hs
        (fun _ => Complex.natCast_mem_slitPlane.mpr hn)
    have hnpow_ne : ∀ t : ℝ,
        (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro t
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast hn)
    have hterm : Continuous
        (fun t : ℝ =>
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((c : ℂ) + (t : ℂ) * Complex.I) n) := by
      simp_rw [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnpow hnpow_ne
    exact ((hterm.mul hxpow).div hs hs_ne).aestronglyMeasurable

/-- Absolute convergence on `Re s = c > 1` justifies termwise integration of
the genuine von Mangoldt Dirichlet series over every finite vertical segment. -/
theorem hasSum_integral_sharpPerronSeriesTerm
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    HasSum
      (fun n : ℕ => ∫ t in (-T)..T, sharpPerronSeriesTerm c x n t)
      (∫ t in (-T)..T,
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((c : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hSeries : LSeriesSummable
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (c : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  have hBoundSummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (c : ℂ) n‖ * (x ^ c / c)) :=
    hSeries.norm.mul_right (x ^ c / c)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := sharpPerronSeriesTerm c x)
    (f := fun t =>
      LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((c : ℂ) + (t : ℂ) * Complex.I) *
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          ((c : ℂ) + (t : ℂ) * Complex.I))
    (bound := fun n _t =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (c : ℂ) n‖ * (x ^ c / c)) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact aestronglyMeasurable_sharpPerronSeriesTerm hc0 hx n T
  · intro n
    exact ae_of_all _ fun t _ht => norm_sharpPerronSeriesTerm_le hc0 hx n t
  · exact ae_of_all _ fun _t _ht => hBoundSummable
  · simp only [tsum_mul_right]
    exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ht => by
      have hsRe : 1 < ((c : ℂ) + (t : ℂ) * Complex.I).re := by
        simpa using hc
      have hAt :=
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hsRe).LSeriesHasSum
      simpa [sharpPerronSeriesTerm, mul_div_assoc] using hAt.mul_right
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          ((c : ℂ) + (t : ℂ) * Complex.I))

/-- The right-line sharp Perron integral is the sum of the integrated
von-Mangoldt monomials. -/
theorem sharpPerron_rightLine_eq_tsum_integrals
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    (∫ t in (-T)..T,
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((c : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)) =
      ∑' n : ℕ, ∫ t in (-T)..T, sharpPerronSeriesTerm c x n t := by
  exact (hasSum_integral_sharpPerronSeriesTerm hc hx).tsum_eq.symm

/-- Each integrated Dirichlet-series term is exactly its von Mangoldt
coefficient times the sharp Perron kernel. -/
theorem normalized_integral_sharpPerronSeriesTerm_eq
    {c T x : ℝ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-T)..T, sharpPerronSeriesTerm c x n t) =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        sharpPerronKernel c T x n := by
  by_cases hn : n = 0
  · subst n
    simp [sharpPerronSeriesTerm, LSeries.term_def]
  · simp only [sharpPerronSeriesTerm]
    simp_rw [LSeries.term_of_ne_zero hn]
    rw [sharpPerronKernel]
    calc
      (1 / (2 * Real.pi) : ℂ) *
          ∫ t in (-T)..T,
            (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
              (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                ((c : ℂ) + (t : ℂ) * Complex.I)
          = (1 / (2 * Real.pi) : ℂ) *
              ∫ t in (-T)..T,
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                    (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                      ((c : ℂ) + (t : ℂ) * Complex.I)) := by
                congr 1
                apply intervalIntegral.integral_congr
                intro t _ht
                ring
      _ = (1 / (2 * Real.pi) : ℂ) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ∫ t in (-T)..T,
                (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                  (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                    ((c : ℂ) + (t : ℂ) * Complex.I)) := by
              rw [intervalIntegral.integral_const_mul]
      _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((1 / (2 * Real.pi) : ℂ) *
              ∫ t in (-T)..T,
                (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                  (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                    ((c : ℂ) + (t : ℂ) * Complex.I)) := by ring

/-- The normalized right-line integral of the genuine logarithmic derivative
is the infinite von Mangoldt-weighted sum of finite-height Perron kernels. -/
theorem sharpPerron_logDerivative_eq_tsum_kernels
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-T)..T,
          (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
              riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)) *
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
              ((c : ℂ) + (t : ℂ) * Complex.I)) =
      ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel c T x n := by
  have hSeries := hasSum_integral_sharpPerronSeriesTerm (T := T) hc hx
  have hScaled := hSeries.mul_left (1 / (2 * Real.pi) : ℂ)
  have hKernels : HasSum
      (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n)
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-T)..T,
          LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              ((c : ℂ) + (t : ℂ) * Complex.I) *
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
              ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    refine HasSum.congr_fun hScaled (fun n => ?_)
    exact
      (normalized_integral_sharpPerronSeriesTerm_eq
        (c := c) (T := T) (x := x) n).symm
  rw [hKernels.tsum_eq]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  have hsRe : 1 < ((c : ℂ) + (t : ℂ) * Complex.I).re := by
    simpa using hc
  dsimp only
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsRe]

end GafniTao
