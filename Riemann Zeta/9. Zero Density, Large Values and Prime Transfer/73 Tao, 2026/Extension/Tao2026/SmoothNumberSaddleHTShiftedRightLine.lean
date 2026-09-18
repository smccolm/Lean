import Tao2026.SmoothNumberSaddleHTShiftedPerron
import GafniTao.SharpPerronSeries

/-!
# Exact shifted Perron right-line identity for the HT transform

This module carries the von Mangoldt Dirichlet series through the finite
vertical integral after the Hildebrand--Tenenbaum shift.  For an initial
line `Re z = c` with `1 < Re s + c`, it identifies the logarithmic-derivative
integral with the weighted frozen sharp-Perron kernels.  The exact cutoff
then gives a termwise error identity for the source transform at
`s = 1 - beta + i*t`.

No contour displacement or zero-free-region estimate is asserted here.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTShiftedMangoldtCoefficient (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n

private noncomputable def shiftedPerronSeriesTerm
    (c y : ℝ) (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (s + ((c : ℂ) + (u : ℂ) * Complex.I)) n *
    (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
      ((c : ℂ) + (u : ℂ) * Complex.I)

noncomputable def smoothSaddleHTShiftedPerronKernel
    (c T y : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  smoothSaddleHTShiftedMangoldtCoefficient s n *
    GafniTao.sharpPerronKernel c T y n

private theorem norm_LSeriesTerm_shifted_vertical_eq
    {c u : ℝ} (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (s + ((c : ℂ) + (u : ℂ) * Complex.I)) n‖ =
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((s.re + c : ℝ) : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [norm_div]
    congr 1
    change
      ‖((n : ℝ) : ℂ) ^ (s + ((c : ℂ) + (u : ℂ) * Complex.I))‖ =
        ‖((n : ℝ) : ℂ) ^ (((s.re + c : ℝ) : ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
    simp

private theorem norm_shiftedPerronSeriesTerm_le
    {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (s : ℂ) (n : ℕ) (u : ℝ) :
    ‖shiftedPerronSeriesTerm c y s n u‖ ≤
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((s.re + c : ℝ) : ℂ) n‖ * (y ^ c / c) := by
  have hzNorm : c ≤ ‖(c : ℂ) + (u : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + (u : ℂ) * Complex.I)
    simpa [abs_of_pos hc] using h
  have hyNorm :
      ‖(y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)‖ = y ^ c := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hy
      ((c : ℂ) + (u : ℂ) * Complex.I)
  rw [shiftedPerronSeriesTerm, norm_div, norm_mul,
    norm_LSeriesTerm_shifted_vertical_eq s n, hyNorm, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.le c)) hc hzNorm

private theorem aestronglyMeasurable_shiftedPerronSeriesTerm
    {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (s : ℂ) (n : ℕ) (T : ℝ) :
    AEStronglyMeasurable (shiftedPerronSeriesTerm c y s n)
      (volume.restrict (Set.uIoc (-T) T)) := by
  have hz : Continuous (fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) := by
    fun_prop
  have hz_ne : ∀ u : ℝ, (c : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro u h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hypow : Continuous
      (fun u : ℝ => (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)) := by
    exact Continuous.cpow continuous_const hz
      (fun _ => Complex.ofReal_mem_slitPlane.mpr hy)
  by_cases hn : n = 0
  · subst n
    have hzero : shiftedPerronSeriesTerm c y s 0 = fun _ : ℝ => (0 : ℂ) := by
      funext u
      simp [shiftedPerronSeriesTerm, LSeries.term_def]
    rw [hzero]
    exact aestronglyMeasurable_const
  · have hnpow : Continuous (fun u : ℝ =>
        (n : ℂ) ^ (s + ((c : ℂ) + (u : ℂ) * Complex.I))) := by
      exact Continuous.cpow continuous_const (continuous_const.add hz)
        (fun _ => Complex.natCast_mem_slitPlane.mpr hn)
    have hnpow_ne : ∀ u : ℝ,
        (n : ℂ) ^ (s + ((c : ℂ) + (u : ℂ) * Complex.I)) ≠ 0 := by
      intro u
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast hn)
    have hterm : Continuous (fun u : ℝ =>
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (s + ((c : ℂ) + (u : ℂ) * Complex.I)) n) := by
      simp_rw [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnpow hnpow_ne
    exact ((hterm.mul hypow).div hz hz_ne).aestronglyMeasurable

private theorem hasSum_integral_shiftedPerronSeriesTerm
    {c T y : ℝ} {s : ℂ} (hc : 1 < s.re + c) (hc0 : 0 < c) (hy : 0 < y) :
    HasSum
      (fun n : ℕ => ∫ u in (-T)..T, shiftedPerronSeriesTerm c y s n u)
      (∫ u in (-T)..T,
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            (s + ((c : ℂ) + (u : ℂ) * Complex.I)) *
          (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
            ((c : ℂ) + (u : ℂ) * Complex.I)) := by
  have hSeries : LSeriesSummable
      (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((s.re + c : ℝ) : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  have hBoundSummable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((s.re + c : ℝ) : ℂ) n‖ * (y ^ c / c)) :=
    hSeries.norm.mul_right (y ^ c / c)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := shiftedPerronSeriesTerm c y s)
    (f := fun u =>
      LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (s + ((c : ℂ) + (u : ℂ) * Complex.I)) *
        (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
          ((c : ℂ) + (u : ℂ) * Complex.I))
    (bound := fun n _u =>
      ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((s.re + c : ℝ) : ℂ) n‖ * (y ^ c / c)) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact aestronglyMeasurable_shiftedPerronSeriesTerm hc0 hy s n T
  · intro n
    exact ae_of_all _ fun u _hu => norm_shiftedPerronSeriesTerm_le hc0 hy s n u
  · exact ae_of_all _ fun _u _hu => hBoundSummable
  · simp only [tsum_mul_right]
    exact intervalIntegrable_const
  · exact ae_of_all _ fun u _hu => by
      have hzRe : 1 <
          (s + ((c : ℂ) + (u : ℂ) * Complex.I)).re := by
        simpa using hc
      have hAt :=
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hzRe).LSeriesHasSum
      simpa [shiftedPerronSeriesTerm, mul_div_assoc] using hAt.mul_right
        ((y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
          ((c : ℂ) + (u : ℂ) * Complex.I))

private theorem normalized_integral_shiftedPerronSeriesTerm_eq
    {c T y : ℝ} {s : ℂ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ u in (-T)..T, shiftedPerronSeriesTerm c y s n u) =
      smoothSaddleHTShiftedPerronKernel c T y s n := by
  by_cases hn : n = 0
  · subst n
    simp [shiftedPerronSeriesTerm, smoothSaddleHTShiftedPerronKernel,
      smoothSaddleHTShiftedMangoldtCoefficient, LSeries.term_def]
  · simp only [shiftedPerronSeriesTerm, smoothSaddleHTShiftedPerronKernel,
      smoothSaddleHTShiftedMangoldtCoefficient]
    simp_rw [LSeries.term_of_ne_zero hn]
    rw [GafniTao.sharpPerronKernel]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    calc
      (1 / (2 * Real.pi) : ℂ) *
          ∫ u in (-T)..T,
            (ArithmeticFunction.vonMangoldt n : ℂ) /
                  (n : ℂ) ^ (s + ((c : ℂ) + (u : ℂ) * Complex.I)) *
                (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                  ((c : ℂ) + (u : ℂ) * Complex.I) =
          (1 / (2 * Real.pi) : ℂ) *
            ∫ u in (-T)..T,
              ((ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s) *
                ((y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                  (n : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                    ((c : ℂ) + (u : ℂ) * Complex.I)) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro u _hu
            dsimp only
            rw [Complex.cpow_add _ _ hnC]
            ring
      _ = (1 / (2 * Real.pi) : ℂ) *
            (((ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s) *
              ∫ u in (-T)..T,
                (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                  (n : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                    ((c : ℂ) + (u : ℂ) * Complex.I)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ((ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s) *
            ((1 / (2 * Real.pi) : ℂ) *
              ∫ u in (-T)..T,
                (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                  (n : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                    ((c : ℂ) + (u : ℂ) * Complex.I)) := by ring

theorem smoothSaddleHTShiftedPerron_logDerivative_eq_tsum_kernels
    {c T y : ℝ} {s : ℂ} (hc : 1 < s.re + c) (hc0 : 0 < c) (hy : 0 < y) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ u in (-T)..T,
          (-deriv riemannZeta
                (s + ((c : ℂ) + (u : ℂ) * Complex.I)) /
              riemannZeta
                (s + ((c : ℂ) + (u : ℂ) * Complex.I))) *
            (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
              ((c : ℂ) + (u : ℂ) * Complex.I)) =
      ∑' n : ℕ, smoothSaddleHTShiftedPerronKernel c T y s n := by
  have hSeries := hasSum_integral_shiftedPerronSeriesTerm
    (T := T) hc hc0 hy
  have hScaled := hSeries.mul_left (1 / (2 * Real.pi) : ℂ)
  have hKernels : HasSum
      (fun n : ℕ => smoothSaddleHTShiftedPerronKernel c T y s n)
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ u in (-T)..T,
          LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (s + ((c : ℂ) + (u : ℂ) * Complex.I)) *
            (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
              ((c : ℂ) + (u : ℂ) * Complex.I)) := by
    refine HasSum.congr_fun hScaled (fun n => ?_)
    exact (normalized_integral_shiftedPerronSeriesTerm_eq n).symm
  rw [hKernels.tsum_eq]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only
  have hzRe : 1 <
      (s + ((c : ℂ) + (u : ℂ) * Complex.I)).re := by
    simpa using hc
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hzRe]

noncomputable def smoothSaddleHTShiftedPerronCutoff
    (y : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  smoothSaddleHTShiftedMangoldtCoefficient s n *
    GafniTao.sharpPerronCutoff (y : ℝ) n

theorem tsum_smoothSaddleHTShiftedPerronCutoff_eq_sourceDirichletSum
    {y : ℕ} (hy : 1 ≤ y) (s : ℂ) :
    ∑' n : ℕ, smoothSaddleHTShiftedPerronCutoff y s n =
      smoothSaddleHTSourceDirichletSum y s := by
  rw [tsum_eq_sum (s := Finset.Icc 0 y)]
  · unfold smoothSaddleHTSourceDirichletSum
    have hset : Finset.Icc 0 y = insert 0 (Finset.Icc 1 y) := by
      ext n
      simp
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp only [smoothSaddleHTShiftedPerronCutoff,
      smoothSaddleHTShiftedMangoldtCoefficient,
      LSeries.term_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 :=
      Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1
    have hny : (n : ℝ) ≤ y := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    simp [GafniTao.sharpPerronCutoff, hny, LSeries.term_of_ne_zero hn0]
  · intro n hn
    have hny : ¬ (n : ℝ) ≤ y := by
      exact_mod_cast (show ¬ n ≤ y by
        intro hle
        exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hle⟩))
    simp [smoothSaddleHTShiftedPerronCutoff,
      GafniTao.sharpPerronCutoff, hny]

theorem summable_smoothSaddleHTShiftedPerronKernel
    {c T y : ℝ} {s : ℂ} (hc : 1 < s.re + c) (hc0 : 0 < c) (hy : 0 < y) :
    Summable (fun n : ℕ =>
      smoothSaddleHTShiftedPerronKernel c T y s n) := by
  have hSeries := hasSum_integral_shiftedPerronSeriesTerm
    (T := T) hc hc0 hy
  have hScaled := hSeries.mul_left (1 / (2 * Real.pi) : ℂ)
  exact (HasSum.congr_fun hScaled (fun n =>
    (normalized_integral_shiftedPerronSeriesTerm_eq n).symm)).summable

theorem summable_smoothSaddleHTShiftedPerronCutoff (y : ℕ) (s : ℂ) :
    Summable (fun n : ℕ => smoothSaddleHTShiftedPerronCutoff y s n) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 0 y)
  intro n hn
  have hny : ¬ (n : ℝ) ≤ y := by
    exact_mod_cast (show ¬ n ≤ y by
      intro hle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hle⟩))
  simp [smoothSaddleHTShiftedPerronCutoff,
    GafniTao.sharpPerronCutoff, hny]

theorem smoothSaddleHTShiftedPerronKernel_sub_cutoff_factor
    (c T : ℝ) (y : ℕ) (s : ℂ) (n : ℕ) :
    smoothSaddleHTShiftedPerronKernel c T y s n -
        smoothSaddleHTShiftedPerronCutoff y s n =
      smoothSaddleHTShiftedMangoldtCoefficient s n *
        (GafniTao.sharpPerronKernel c T y n -
          GafniTao.sharpPerronCutoff (y : ℝ) n) := by
  unfold smoothSaddleHTShiftedPerronKernel
    smoothSaddleHTShiftedPerronCutoff
  ring

theorem smoothSaddleHTShiftedPerron_logDerivative_sub_sourceDirichletSum_eq_tsum_cutoffError
    {c T : ℝ} {y : ℕ} {s : ℂ} (hc : 1 < s.re + c)
    (hc0 : 0 < c) (hy : 1 ≤ y) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ u in (-T)..T,
            (-deriv riemannZeta
                  (s + ((c : ℂ) + (u : ℂ) * Complex.I)) /
                riemannZeta
                  (s + ((c : ℂ) + (u : ℂ) * Complex.I))) *
              (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                ((c : ℂ) + (u : ℂ) * Complex.I)) -
        smoothSaddleHTSourceDirichletSum y s =
      ∑' n : ℕ,
        smoothSaddleHTShiftedMangoldtCoefficient s n *
          (GafniTao.sharpPerronKernel c T y n -
            GafniTao.sharpPerronCutoff (y : ℝ) n) := by
  have hy0 : (0 : ℝ) < y := by positivity
  have hyCast : (y : ℂ) = (((y : ℝ) : ℂ)) := by norm_num
  rw [hyCast]
  rw [smoothSaddleHTShiftedPerron_logDerivative_eq_tsum_kernels
    (y := (y : ℝ)) (s := s) hc hc0 hy0]
  rw [← tsum_smoothSaddleHTShiftedPerronCutoff_eq_sourceDirichletSum hy s]
  rw [← (summable_smoothSaddleHTShiftedPerronKernel hc hc0 hy0).tsum_sub
    (summable_smoothSaddleHTShiftedPerronCutoff y s)]
  congr 1
  funext n
  exact smoothSaddleHTShiftedPerronKernel_sub_cutoff_factor c T y s n

theorem smoothSaddleHTSource_shiftedPerron_error_identity
    {c T : ℝ} {y : ℕ} {beta t : ℝ} (hbetaC : beta < c)
    (hc0 : 0 < c) (hy : 1 ≤ y) :
    (1 / (2 * Real.pi) : ℂ) *
          (∫ u in (-T)..T,
            (-deriv riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((c : ℂ) + (u : ℂ) * Complex.I)) /
                riemannZeta
                  (smoothSaddleHTSourceExponent beta t +
                    ((c : ℂ) + (u : ℂ) * Complex.I))) *
              (y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I) /
                ((c : ℂ) + (u : ℂ) * Complex.I)) -
        smoothSaddleHTMangoldtTransform y beta t =
      ∑' n : ℕ,
        smoothSaddleHTShiftedMangoldtCoefficient
            (smoothSaddleHTSourceExponent beta t) n *
          (GafniTao.sharpPerronKernel c T y n -
            GafniTao.sharpPerronCutoff (y : ℝ) n) := by
  rw [smoothSaddleHTMangoldtTransform_eq_sourceDirichletSum]
  apply smoothSaddleHTShiftedPerron_logDerivative_sub_sourceDirichletSum_eq_tsum_cutoffError
    (hc0 := hc0) (hy := hy)
  simp
  linarith

end

end Tao2026
