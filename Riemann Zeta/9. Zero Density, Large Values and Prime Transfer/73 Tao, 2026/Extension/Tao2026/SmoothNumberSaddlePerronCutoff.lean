import Tao2026.SmoothNumberSaddlePerronLine
import GafniTao.SharpPerronEndpoint

/-!
# The smooth-number sharp Perron series

This module passes the absolutely convergent smooth-number Dirichlet series
through the finite vertical Perron integral.  The result identifies the
literal saddle-point line from `SmoothNumberSaddlePerronLine` with the sum of
the frozen, coefficient-free sharp-Perron kernels.  Consequently the physical
cutoff estimates already proved for those kernels apply term by term to the
smooth-number coefficients.
-/

open scoped BigOperators Interval
open MeasureTheory

namespace Tao2026

noncomputable section

/-- A Fourier Rankin weight is exactly the reciprocal complex Dirichlet
monomial on the vertical line. -/
theorem smoothFourierWeight_neg_eq_cpow_div
    {n : ℕ} (hn : n ≠ 0) (sigma t : ℝ) :
    smoothFourierWeight sigma (-t) n =
      1 / (n : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I) := by
  unfold smoothFourierWeight
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
  rw [← Complex.natCast_log]
  rw [one_div, ← Complex.exp_neg]
  rw [Real.rpow_def_of_pos (by positivity), Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The numerator monomial on the vertical line separates into its positive
Rankin magnitude and its Fourier phase. -/
theorem ofReal_cpow_vertical_eq_rpow_mul_exp
    {x : ℝ} (hx : 0 < x) (sigma t : ℝ) :
    (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I) =
      ((x ^ sigma : ℝ) : ℂ) *
        Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  rw [mul_add, Complex.exp_add]
  rw [Complex.ofReal_mul, Real.rpow_def_of_pos hx, Complex.ofReal_exp]
  congr 1
  · push_cast
    ring_nf
  · ring_nf

/-- One unweighted smooth-number term in the finite sharp-Perron integral. -/
private noncomputable def smoothSharpPerronSeriesTerm
    {k : ℕ} (sigma x : ℝ) (n : Nat.smoothNumbers k) (t : ℝ) : ℂ :=
  (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I) /
    (n.1 : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I) /
      ((sigma : ℂ) + (t : ℂ) * Complex.I)

private theorem norm_smoothSharpPerronSeriesTerm_le
    {k : ℕ} {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x)
    (n : Nat.smoothNumbers k) (t : ℝ) :
    ‖smoothSharpPerronSeriesTerm sigma x n t‖ ≤
      (n.1 : ℝ) ^ (-sigma) * (x ^ sigma / sigma) := by
  have hn0 : n.1 ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers n.2
  have hnPos : 0 < (n.1 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hsNorm : sigma ≤
      ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm
      ((sigma : ℂ) + (t : ℂ) * Complex.I)
    simpa [abs_of_pos hsigma] using h
  have hsPos : 0 < ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ :=
    hsigma.trans_le hsNorm
  rw [smoothSharpPerronSeriesTerm, norm_div, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hnNorm := Complex.norm_cpow_eq_rpow_re_of_pos hnPos
    ((sigma : ℂ) + (t : ℂ) * Complex.I)
  change _ / ‖((n.1 : ℝ) : ℂ) ^
      ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ / _ ≤ _
  rw [hnNorm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero]
  rw [add_zero, Real.rpow_neg hnPos.le]
  have hnum : 0 ≤ x ^ sigma / (n.1 : ℝ) ^ sigma :=
    div_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hnPos.le _)
  have hdiv := div_le_div_of_nonneg_left hnum hsigma hsNorm
  calc
    x ^ sigma / (n.1 : ℝ) ^ sigma /
        ‖(sigma : ℂ) + (t : ℂ) * Complex.I‖ ≤
      (x ^ sigma / (n.1 : ℝ) ^ sigma) / sigma := hdiv
    _ = ((n.1 : ℝ) ^ sigma)⁻¹ * (x ^ sigma / sigma) := by ring_nf

private theorem aestronglyMeasurable_smoothSharpPerronSeriesTerm
    {k : ℕ} {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x)
    (n : Nat.smoothNumbers k) (T : ℝ) :
    AEStronglyMeasurable (smoothSharpPerronSeriesTerm sigma x n)
      (volume.restrict (Set.uIoc (-T) T)) := by
  have hs : Continuous (fun t : ℝ =>
      (sigma : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hs_ne : ∀ t : ℝ,
      (sigma : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, Complex.zero_re] at hre
    linarith
  have hxpow : Continuous (fun t : ℝ =>
      (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I)) :=
    Continuous.cpow continuous_const hs
      (fun _ => Complex.ofReal_mem_slitPlane.mpr hx)
  have hn0 : n.1 ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers n.2
  have hnpow : Continuous (fun t : ℝ =>
      (n.1 : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I)) :=
    Continuous.cpow continuous_const hs
      (fun _ => Complex.natCast_mem_slitPlane.mpr hn0)
  have hnpow_ne : ∀ t : ℝ,
      (n.1 : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast hn0)
  exact ((hxpow.div hnpow hnpow_ne).div hs hs_ne).aestronglyMeasurable

/-- Absolute convergence of the smooth Dirichlet series justifies termwise
integration on every finite vertical segment in the positive half-plane. -/
private theorem hasSum_integral_smoothSharpPerronSeriesTerm
    {k : ℕ} {sigma T x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    HasSum
      (fun n : Nat.smoothNumbers k =>
        ∫ t in (-T)..T, smoothSharpPerronSeriesTerm sigma x n t)
      (∫ t in (-T)..T,
        (((x ^ sigma : ℝ) : ℂ) *
            smoothFourierDirichletSeries k sigma (-t) *
            Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
          ((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
  have hBoundSummable : Summable (fun n : Nat.smoothNumbers k =>
      (n.1 : ℝ) ^ (-sigma) * (x ^ sigma / sigma)) :=
    (summable_smoothDirichletSeries_and_eq_eulerProduct k hsigma).1.mul_right _
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := smoothSharpPerronSeriesTerm sigma x)
    (f := fun t =>
      (((x ^ sigma : ℝ) : ℂ) *
          smoothFourierDirichletSeries k sigma (-t) *
          Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
        ((sigma : ℂ) + (t : ℂ) * Complex.I))
    (bound := fun n _t =>
      (n.1 : ℝ) ^ (-sigma) * (x ^ sigma / sigma)) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact aestronglyMeasurable_smoothSharpPerronSeriesTerm hsigma hx n T
  · intro n
    exact ae_of_all _ fun t _ht =>
      norm_smoothSharpPerronSeriesTerm_le hsigma hx n t
  · exact ae_of_all _ fun _t _ht => hBoundSummable
  · simp only [tsum_mul_right]
    exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ht => by
      have hSeries := summable_smoothFourierDirichletSeries k hsigma (-t)
      have hScaled := hSeries.hasSum.mul_right
        ((((x ^ sigma : ℝ) : ℂ) *
          Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
            ((sigma : ℂ) + (t : ℂ) * Complex.I))
      have hScaled' : HasSum
          (fun n : Nat.smoothNumbers k => smoothFourierWeight sigma (-t) n.1 *
            ((((x ^ sigma : ℝ) : ℂ) *
              Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
                ((sigma : ℂ) + (t : ℂ) * Complex.I)))
          (smoothFourierDirichletSeries k sigma (-t) *
            ((((x ^ sigma : ℝ) : ℂ) *
              Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
                ((sigma : ℂ) + (t : ℂ) * Complex.I))) := by
        simpa only [smoothFourierDirichletSeries] using hScaled
      have hCong : HasSum
          (fun n : Nat.smoothNumbers k =>
            smoothSharpPerronSeriesTerm sigma x n t)
          (smoothFourierDirichletSeries k sigma (-t) *
            ((((x ^ sigma : ℝ) : ℂ) *
              Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
                ((sigma : ℂ) + (t : ℂ) * Complex.I))) := by
        refine HasSum.congr_fun hScaled' (fun n => ?_)
        rw [smoothSharpPerronSeriesTerm,
          smoothFourierWeight_neg_eq_cpow_div
            (Nat.ne_zero_of_mem_smoothNumbers n.2),
          ofReal_cpow_vertical_eq_rpow_mul_exp hx]
        ring_nf
      convert hCong using 1
      ring_nf

/-- The normalized integral of one smooth-number monomial is exactly the
frozen sharp-Perron kernel. -/
private theorem normalized_integral_smoothSharpPerronSeriesTerm_eq
    {k : ℕ} {sigma T x : ℝ} (n : Nat.smoothNumbers k) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-T)..T, smoothSharpPerronSeriesTerm sigma x n t) =
      GafniTao.sharpPerronKernel sigma T x n.1 := by
  rfl

/-- The unnormalized smooth-number Perron line is exactly the sum of the
coefficient-free finite-height sharp-Perron kernels. -/
theorem smoothSharpPerron_rightLine_eq_tsum_kernels
    {k : ℕ} {sigma T x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-T)..T,
          (((x ^ sigma : ℝ) : ℂ) *
              smoothFourierDirichletSeries k sigma (-t) *
              Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)) /
            ((sigma : ℂ) + (t : ℂ) * Complex.I)) =
      ∑' n : Nat.smoothNumbers k,
        GafniTao.sharpPerronKernel sigma T x n.1 := by
  have hSeries := hasSum_integral_smoothSharpPerronSeriesTerm
    (k := k) (T := T) hsigma hx
  have hScaled := hSeries.mul_left (1 / (2 * Real.pi) : ℂ)
  exact (HasSum.congr_fun hScaled (fun n =>
    (normalized_integral_smoothSharpPerronSeriesTerm_eq n).symm)).tsum_eq.symm

/-- The canonical inclusion of the finite smooth range into the ambient
smooth-number subtype. -/
private def smoothNumbersUpToEmbedding (X y : ℕ) :
    {n // n ∈ Nat.smoothNumbersUpTo X (y + 1)} ↪
      Nat.smoothNumbers (y + 1) :=
  ⟨fun n => ⟨n.1, (Nat.mem_smoothNumbersUpTo.mp n.2).2⟩,
    fun a b hab => by
      have hv : (a.val : ℕ) = b.val := congrArg
        (fun z : Nat.smoothNumbers (y + 1) => z.val) hab
      exact Subtype.ext hv⟩

/-- The finite set of positive source-smooth integers at most `X`, regarded
as a finset in the ambient smooth-number subtype. -/
noncomputable def smoothNumbersUpToSubtype (X y : ℕ) :
    Finset (Nat.smoothNumbers (y + 1)) :=
  (Nat.smoothNumbersUpTo X (y + 1)).attach.map
    (smoothNumbersUpToEmbedding X y)

@[simp] theorem mem_smoothNumbersUpToSubtype
    {X y : ℕ} {n : Nat.smoothNumbers (y + 1)} :
    n ∈ smoothNumbersUpToSubtype X y ↔ n.1 ≤ X := by
  unfold smoothNumbersUpToSubtype
  rw [Finset.mem_map]
  constructor
  · rintro ⟨m, _hm, hem⟩
    have hv : (m.val : ℕ) = n.val := congrArg
      (fun z : Nat.smoothNumbers (y + 1) => z.val) hem
    rw [← hv]
    exact (Nat.mem_smoothNumbersUpTo.mp m.2).1
  · intro hnX
    let m : {m // m ∈ Nat.smoothNumbersUpTo X (y + 1)} :=
      ⟨n.1, Nat.mem_smoothNumbersUpTo.mpr ⟨hnX, n.2⟩⟩
    refine ⟨m, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- The source-smooth sharp cutoff, with the right endpoint included. -/
noncomputable def smoothSharpPerronCutoff
    (X y : ℕ) (n : Nat.smoothNumbers (y + 1)) : ℂ :=
  GafniTao.sharpPerronCutoff (X : ℝ) n.1

/-- The exact cutoff series counts source-smooth integers, including an
integral endpoint. -/
theorem tsum_smoothSharpPerronCutoff_eq_psiNat (X y : ℕ) :
    ∑' n : Nat.smoothNumbers (y + 1), smoothSharpPerronCutoff X y n =
      (psiNat X y : ℂ) := by
  rw [tsum_eq_sum (s := smoothNumbersUpToSubtype X y)]
  · calc
      ∑ n ∈ smoothNumbersUpToSubtype X y, smoothSharpPerronCutoff X y n =
          ∑ _n ∈ smoothNumbersUpToSubtype X y, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnX : n.1 ≤ X := mem_smoothNumbersUpToSubtype.mp hn
            simp [smoothSharpPerronCutoff, GafniTao.sharpPerronCutoff,
              show (n.1 : ℝ) ≤ X by exact_mod_cast hnX]
      _ = ((smoothNumbersUpToSubtype X y).card : ℂ) := by simp
      _ = (psiNat X y : ℂ) := by
            congr 1
            simp [smoothNumbersUpToSubtype, psiNat]
  · intro n hn
    have hnX : ¬ n.1 ≤ X := by
      simpa only [mem_smoothNumbersUpToSubtype] using hn
    have hnX' : ¬ (n.1 : ℝ) ≤ X := by exact_mod_cast hnX
    simp [smoothSharpPerronCutoff, GafniTao.sharpPerronCutoff, hnX']

/-- Absolute convergence of the smooth-number sharp-Perron kernel series. -/
theorem summable_smoothSharpPerronKernel
    {k : ℕ} {sigma T x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    Summable (fun n : Nat.smoothNumbers k =>
      GafniTao.sharpPerronKernel sigma T x n.1) := by
  have hSeries := hasSum_integral_smoothSharpPerronSeriesTerm
    (k := k) (T := T) hsigma hx
  have hScaled := hSeries.mul_left (1 / (2 * Real.pi) : ℂ)
  exact (HasSum.congr_fun hScaled (fun n =>
    (normalized_integral_smoothSharpPerronSeriesTerm_eq n).symm)).summable

/-- The source-smooth cutoff series is finite, hence summable. -/
theorem summable_smoothSharpPerronCutoff (X y : ℕ) :
    Summable (fun n : Nat.smoothNumbers (y + 1) =>
      smoothSharpPerronCutoff X y n) := by
  apply summable_of_ne_finset_zero (s := smoothNumbersUpToSubtype X y)
  intro n hn
  have hnX : ¬ n.1 ≤ X := by
    simpa only [mem_smoothNumbersUpToSubtype] using hn
  have hnX' : ¬ (n.1 : ℝ) ≤ X := by exact_mod_cast hnX
  simp [smoothSharpPerronCutoff, GafniTao.sharpPerronCutoff, hnX']

/-- Exact decomposition of the smooth-number finite-height Perron error into
the termwise frozen-kernel cutoff errors. -/
theorem smoothSharpPerron_tsum_sub_psiNat_eq_tsum_cutoffError
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hX : 1 ≤ X) :
    (∑' n : Nat.smoothNumbers (y + 1),
        GafniTao.sharpPerronKernel sigma T X n.1) - (psiNat X y : ℂ) =
      ∑' n : Nat.smoothNumbers (y + 1),
        (GafniTao.sharpPerronKernel sigma T X n.1 -
          smoothSharpPerronCutoff X y n) := by
  rw [← tsum_smoothSharpPerronCutoff_eq_psiNat X y]
  exact ((summable_smoothSharpPerronKernel hsigma
    (show (0 : ℝ) < X by positivity)).tsum_sub
      (summable_smoothSharpPerronCutoff X y)).symm

/-- Below the endpoint, the source-smooth cutoff error inherits the frozen
physical-variable logarithmic bound. -/
theorem norm_smoothSharpPerronKernel_sub_cutoff_le_of_lt
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hT : 0 < T)
    (hX : 1 ≤ X) (n : Nat.smoothNumbers (y + 1)) (hnX : n.1 < X) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤
      ((X : ℝ) / n.1) ^ sigma /
        (Real.pi * T * Real.log ((X : ℝ) / n.1)) := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hnXreal : (n.1 : ℝ) < X := by exact_mod_cast hnX
  have hcut : smoothSharpPerronCutoff X y n = 1 := by
    simp [smoothSharpPerronCutoff, GafniTao.sharpPerronCutoff,
      show (n.1 : ℝ) ≤ X by linarith]
  rw [hcut]
  exact GafniTao.norm_sharpPerronKernel_sub_one_le_of_natCast_lt
    hsigma hT (show (0 : ℝ) < X by positivity) hn hnXreal

/-- Above the endpoint, the source-smooth cutoff error inherits the frozen
physical-variable logarithmic bound. -/
theorem norm_smoothSharpPerronKernel_sub_cutoff_le_of_gt
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hT : 0 < T)
    (hX : 1 ≤ X) (n : Nat.smoothNumbers (y + 1)) (hXn : X < n.1) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤
      ((X : ℝ) / n.1) ^ sigma /
        (Real.pi * T * (-Real.log ((X : ℝ) / n.1))) := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hXnReal : (X : ℝ) < n.1 := by exact_mod_cast hXn
  have hcut : smoothSharpPerronCutoff X y n = 0 := by
    simp [smoothSharpPerronCutoff, GafniTao.sharpPerronCutoff,
      show ¬ (n.1 : ℝ) ≤ X by linarith]
  rw [hcut, sub_zero]
  exact GafniTao.norm_sharpPerronKernel_le_of_natCast_lt
    hsigma hT (show (0 : ℝ) < X by positivity) hn hXnReal

/-- At the integral endpoint the cutoff error is uniformly at most `3/2`,
independently of the Perron height. -/
theorem norm_smoothSharpPerronKernel_sub_cutoff_le_three_halves_of_eq
    {X y : ℕ} {sigma T : ℝ} (hsigma : 0 < sigma) (hX : 1 ≤ X)
    (n : Nat.smoothNumbers (y + 1)) (hnX : n.1 = X) :
    ‖GafniTao.sharpPerronKernel sigma T X n.1 -
        smoothSharpPerronCutoff X y n‖ ≤ (3 / 2 : ℝ) := by
  have hn : 1 ≤ n.1 := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_zero_of_mem_smoothNumbers n.2)
  have hcut : smoothSharpPerronCutoff X y n = 1 := by
    simp [smoothSharpPerronCutoff, GafniTao.sharpPerronCutoff, hnX]
  rw [hcut]
  calc
    ‖GafniTao.sharpPerronKernel sigma T X n.1 - 1‖ ≤
        ‖GafniTao.sharpPerronKernel sigma T X n.1‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ (1 / 2 : ℝ) + 1 := by
      simpa using add_le_add_right
        (GafniTao.norm_sharpPerronKernel_at_natCast_le_half hsigma
          (show (0 : ℝ) < X by positivity) hn (by exact_mod_cast hnX.symm)) 1
    _ = 3 / 2 := by norm_num

/-- Source-facing version: after restoring the saddle normalization, the
literal Perron-line integral is the sharp-Perron kernel series. -/
theorem smoothSaddlePerronLine_eq_tsum_sharpPerronKernels
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (T : ℝ) :
    ∑' n : Nat.smoothNumbers (y + 1),
        GafniTao.sharpPerronKernel (smoothSaddlePoint X y) T X n.1 =
      ((((X : ℝ) ^ smoothSaddlePoint X y : ℝ) : ℂ) *
          (smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) : ℂ) /
          (smoothSaddlePoint X y : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t in (-T)..T, smoothSaddlePerronLineIntegrand X y t) := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have hXpos : (0 : ℝ) < X := by positivity
  have hZpos : 0 < smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) :=
    smoothDirichletSeries_source_pos y hsigma
  rw [← smoothSharpPerron_rightLine_eq_tsum_kernels hsigma hXpos]
  let C : ℂ :=
    (((X : ℝ) ^ smoothSaddlePoint X y : ℝ) : ℂ) *
      (smoothDirichletSeries (y + 1) (smoothSaddlePoint X y) : ℂ) /
      (smoothSaddlePoint X y : ℂ)
  calc
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-T)..T,
          ((((X : ℝ) ^ smoothSaddlePoint X y : ℝ) : ℂ) *
              smoothFourierDirichletSeries (y + 1)
                (smoothSaddlePoint X y) (-t) *
              Complex.exp (((t * Real.log (X : ℝ) : ℝ) : ℂ) *
                Complex.I)) /
            ((smoothSaddlePoint X y : ℂ) + (t : ℂ) * Complex.I)) =
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-T)..T, C * smoothSaddlePerronLineIntegrand X y t) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t _ht
          unfold C smoothSaddlePerronLineIntegrand
          field_simp [hsigma.ne', hZpos.ne']
    _ = C * ((1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-T)..T, smoothSaddlePerronLineIntegrand X y t) := by
          rw [intervalIntegral.integral_const_mul]
          ring_nf
    _ = _ := rfl

end

end Tao2026
