import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import RiemannZeta.GuthMaynard.LargeValuesPoisson

open Complex MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap

namespace RiemannZeta.GuthMaynard

/-!
# Smooth reflection for the Guth--Maynard trace kernel

This module proves the source-normalized finite identities and oscillatory
integral estimates used in Guth--Maynard Lemma 6.2.  In particular, the
Fourier coefficient is first restricted to the common interval used in the
paper and then rescaled so that the remaining oscillatory integral is
independent of the positive Fourier mode.
-/

/-- Falling coefficient in the repeated derivative of `x^z`. -/
noncomputable def gmCpowDerivativeCoeff (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => z * gmCpowDerivativeCoeff (z - 1) n

@[simp]
theorem gmCpowDerivativeCoeff_zero (z : ℂ) :
    gmCpowDerivativeCoeff z 0 = 1 := by
  rfl

theorem gmCpowDerivativeCoeff_succ (z : ℂ) (n : ℕ) :
    gmCpowDerivativeCoeff z (n + 1) =
      z * gmCpowDerivativeCoeff (z - 1) n := by
  rfl

/-- Repeated real derivative of a complex power on the positive axis. -/
theorem iteratedDeriv_ofReal_cpow (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ z) x =
      gmCpowDerivativeCoeff z n * (x : ℂ) ^ (z - n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv :
          deriv (fun y : ℝ => (y : ℂ) ^ z) =ᶠ[nhds x]
            fun y : ℝ => z * (y : ℂ) ^ (z - 1) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        by_cases hz : z = 0
        · subst z
          simp
        · exact Complex.deriv_ofReal_cpow_const hy.ne' hz
      rw [hderiv.iteratedDeriv_eq]
      rw [iteratedDeriv_const_mul_field, ih (z := z - 1)]
      rw [gmCpowDerivativeCoeff_succ]
      have hexponent : z - 1 - (n : ℂ) = z - ((n + 1 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [hexponent]
      ring

/-- Polynomial growth of the falling coefficient, uniform in the exponent. -/
theorem norm_gmCpowDerivativeCoeff_le (z : ℂ) (n : ℕ) :
    ‖gmCpowDerivativeCoeff z n‖ ≤ (‖z‖ + n) ^ n := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [gmCpowDerivativeCoeff_succ, norm_mul]
      have hshift : ‖z - 1‖ + n ≤ ‖z‖ + (n + 1) := by
        have hnorm : ‖z - 1‖ ≤ ‖z‖ + 1 := by
          calc
            ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = ‖z‖ + 1 := by simp
        norm_num at hnorm ⊢
        linarith
      calc
        ‖z‖ * ‖gmCpowDerivativeCoeff (z - 1) n‖ ≤
            ‖z‖ * (‖z - 1‖ + n) ^ n :=
          mul_le_mul_of_nonneg_left (ih (z - 1)) (norm_nonneg _)
        _ ≤ (‖z‖ + (n + 1)) * (‖z‖ + (n + 1)) ^ n := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)
        _ = (‖z‖ + ((n : ℝ) + 1)) ^ (n + 1) := by
          rw [pow_succ']
        _ = (‖z‖ + ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
          norm_num

private noncomputable def gmCutoffSqComplex
    (cutoff : GMSmoothCutoff) (x : ℝ) : ℂ :=
  (cutoff x : ℂ) ^ 2

private theorem contDiff_gmCutoffSqComplex (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (gmCutoffSqComplex cutoff) := by
  exact (Complex.ofRealCLM.contDiff.comp cutoff.smooth).pow 2

private theorem hasCompactSupport_gmCutoffSqComplex
    (cutoff : GMSmoothCutoff) :
    HasCompactSupport (gmCutoffSqComplex cutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hnot
  apply hx
  have hcut : cutoff x = 0 := by
    by_contra hne
    exact hnot (cutoff.support hne)
  simp [gmCutoffSqComplex, hcut]

private noncomputable def gmCutoffSqSchwartz
    (cutoff : GMSmoothCutoff) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmCutoffSqComplex cutoff).toSchwartzMap
    (contDiff_gmCutoffSqComplex cutoff)

@[simp]
private theorem gmCutoffSqSchwartz_apply (cutoff : GMSmoothCutoff) (x : ℝ) :
    gmCutoffSqSchwartz cutoff x = gmCutoffSqComplex cutoff x := rfl

private theorem gmTraceKernel_eq_cutoffSq_mul_cpow
    (cutoff : GMSmoothCutoff) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    gmTraceKernel cutoff t x =
      gmCutoffSqComplex cutoff x * (x : ℂ) ^ ((t : ℂ) * I) := by
  unfold gmTraceKernel gmCutoffSqComplex
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 2
  push_cast
  ring

/-- Uniform derivative bound for the Mellin oscillation on the cutoff
support. -/
theorem norm_iteratedDeriv_ofReal_cpow_mul_I_le
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
      (|t| + n) ^ n := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  rw [iteratedDeriv_ofReal_cpow ((t : ℂ) * I) n hxPos, norm_mul]
  have hcoeff := norm_gmCpowDerivativeCoeff_le ((t : ℂ) * I) n
  have hpow : ‖(x : ℂ) ^ ((t : ℂ) * I - n)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    have hre : (((t : ℂ) * I - n).re) = -(n : ℝ) := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  calc
    ‖gmCpowDerivativeCoeff ((t : ℂ) * I) n‖ *
          ‖(x : ℂ) ^ ((t : ℂ) * I - n)‖ ≤
        (‖((t : ℂ) * I)‖ + n) ^ n * 1 :=
      mul_le_mul hcoeff hpow (norm_nonneg _) (by positivity)
    _ = (|t| + n) ^ n := by
      simp [Real.norm_eq_abs]

private theorem mellinDerivativePower_le (t : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (|t| + k) ^ k ≤
      (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by
  let B : ℝ := (n + 1) * (1 + |t|)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    nlinarith [abs_nonneg t]
  have hbase : |t| + k ≤ B := by
    dsimp only [B]
    have hkReal : (k : ℝ) ≤ n := by exact_mod_cast hkn
    nlinarith [abs_nonneg t]
  calc
    (|t| + k) ^ k ≤ B ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ B ^ n := pow_le_pow_right₀ hBOne hkn
    _ = (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by
      dsimp only [B]
      rw [mul_pow]

private theorem contDiffAt_ofReal_cpow_mul_I
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x := by
  have hEq :
      (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) =ᶠ[nhds x]
        fun y : ℝ => Complex.exp ((((t * Real.log y : ℝ) : ℂ) * I)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
    rw [← Complex.ofReal_log hy.le]
    congr 1
    push_cast
    ring
  have hExp : ContDiffAt ℝ n
      (fun y : ℝ => Complex.exp ((((t * Real.log y : ℝ) : ℂ) * I))) x := by
    have hReal : ContDiffAt ℝ n (fun y : ℝ => t * Real.log y) x :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hx.ne')
    have hComplex : ContDiffAt ℝ n
        (fun y : ℝ => ((t * Real.log y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hReal
    exact (hComplex.mul contDiffAt_const).cexp
  exact hExp.congr_of_eventuallyEq hEq

/-- Guth--Maynard Lemma 4.3 in the exact two-parameter form needed to make
the smooth-reflection frequency truncation uniform. -/
theorem gmTraceKernel_uniform_iteratedFDeriv (cutoff : GMSmoothCutoff)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ n (gmTraceKernel cutoff t) x‖ ≤
        C * (1 + |t|) ^ n := by
  let C : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
        (n + 1 : ℝ) ^ n
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hxLow : x < 1
  · have hzero : gmTraceKernel cutoff t =ᶠ[nhds x] 0 := by
      filter_upwards [Iio_mem_nhds hxLow] with y hy
      simp [gmTraceKernel, gmSmoothCutoff_eq_zero_of_lt_one cutoff hy]
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  by_cases hxHigh : 2 < x
  · have hzero : gmTraceKernel cutoff t =ᶠ[nhds x] 0 := by
      filter_upwards [Ioi_mem_nhds hxHigh] with y hy
      simp [gmTraceKernel,
        gmSmoothCutoff_eq_zero_of_two_le cutoff (le_of_lt hy)]
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  have hxIcc : x ∈ Set.Icc (1 : ℝ) 2 := ⟨le_of_not_gt hxLow, le_of_not_gt hxHigh⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hxIcc.1
  have hlocal : gmTraceKernel cutoff t =ᶠ[nhds x]
      fun y : ℝ => gmCutoffSqComplex cutoff y *
        (y : ℂ) ^ ((t : ℂ) * I) := by
    filter_upwards [Ioi_mem_nhds hxPos] with y hy
    exact gmTraceKernel_eq_cutoffSq_mul_cpow cutoff t hy
  rw [hlocal.iteratedDeriv_eq]
  have hcutSmooth : ContDiffAt ℝ n (gmCutoffSqComplex cutoff) x :=
    (contDiff_gmCutoffSqComplex cutoff).contDiffAt.of_le (by exact_mod_cast le_top)
  have hphaseSmooth := contDiffAt_ofReal_cpow_mul_I t n hxPos
  change ‖iteratedDeriv n
      (gmCutoffSqComplex cutoff * fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
    C * (1 + |t|) ^ n
  rw [iteratedDeriv_mul hcutSmooth hphaseSmooth]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (gmCutoffSqComplex cutoff) x *
          iteratedDeriv (n - i) (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) * iteratedDeriv i (gmCutoffSqComplex cutoff) x *
          iteratedDeriv (n - i) (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
            (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hcut := SchwartzMap.le_seminorm' (𝕜 := ℝ) 0 i
        (gmCutoffSqSchwartz cutoff) x
      simp only [pow_zero, one_mul] at hcut
      change ‖iteratedDeriv i (gmCutoffSqComplex cutoff) x‖ ≤
        SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) at hcut
      have hphase := norm_iteratedDeriv_ofReal_cpow_mul_I_le
        t (n - i) hxIcc.1
      have hpower := mellinDerivativePower_le t (Nat.sub_le n i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        (n.choose i : ℝ) * ‖iteratedDeriv i (gmCutoffSqComplex cutoff) x‖ *
            ‖iteratedDeriv (n - i)
              (fun y : ℝ => (y : ℂ) ^ ((t : ℂ) * I)) x‖ ≤
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
              (|t| + ((n - i : ℕ) : ℝ)) ^ (n - i) := by
            gcongr
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
              ((n + 1 : ℝ) ^ n * (1 + |t|) ^ n) := by
            gcongr
        _ = ((n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (gmCutoffSqSchwartz cutoff) *
              (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by ring
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [Finset.sum_mul]

private theorem integral_norm_iteratedFDeriv_gmTraceKernel_le
    (cutoff : GMSmoothCutoff) (p : ℕ) {D : ℝ}
    (hbound : ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖ ≤
        D * (1 + |t|) ^ p) (t : ℝ) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖) ≤
      D * (1 + |t|) ^ p := by
  let f : ℝ → ℝ := fun x =>
    ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖
  have hfInt : Integrable f := by
    simpa only [f, pow_zero, one_mul] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (gmTraceKernelSchwartz cutoff t) 0 p)
  have hsupport : Function.support f ⊆ Set.Icc (1 : ℝ) 2 := by
    intro x hx
    by_contra hnot
    have hxOutside : x < 1 ∨ 2 < x := by
      by_cases hxLow : x < 1
      · exact Or.inl hxLow
      · exact Or.inr (lt_of_not_ge fun hxUpper => hnot ⟨le_of_not_gt hxLow, hxUpper⟩)
    have hzero : gmTraceKernel cutoff t =ᶠ[nhds x] 0 := by
      rcases hxOutside with hxLow | hxHigh
      · filter_upwards [Iio_mem_nhds hxLow] with y hy
        simp [gmTraceKernel, gmSmoothCutoff_eq_zero_of_lt_one cutoff hy]
      · filter_upwards [Ioi_mem_nhds hxHigh] with y hy
        simp [gmTraceKernel,
          gmSmoothCutoff_eq_zero_of_two_le cutoff (le_of_lt hy)]
    apply hx
    dsimp only [f]
    rw [(hzero.iteratedFDeriv ℝ p).eq_of_nhds]
    simp
  have hEq : f = Set.indicator (Set.Icc (1 : ℝ) 2) f := by
    funext x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
    · simp [hx]
    · have : f x = 0 := not_ne_iff.mp fun hne => hx (hsupport hne)
      simp [Set.indicator, hx, this]
  rw [show (∫ x : ℝ, ‖iteratedFDeriv ℝ p
      (gmTraceKernel cutoff t) x‖) = ∫ x : ℝ, f x by rfl]
  rw [hEq, MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ x : ℝ in Set.Icc 1 2, f x) ≤
        ∫ _x : ℝ in Set.Icc 1 2, D * (1 + |t|) ^ p := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hfInt.integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := ne_of_lt
            (measure_Icc_lt_top : volume (Set.Icc (1 : ℝ) 2) < (⊤ : ENNReal)))
      · exact measurableSet_Icc
      · intro x hx
        exact hbound t x
    _ = D * (1 + |t|) ^ p := by
      simp
      ring

/-- Uniform two-parameter Fourier decay.  The constant depends only on the
fixed cutoff and derivative order, while the complete `t` dependence is the
source polynomial `(1+|t|)^n`. -/
theorem gmTraceFourier_uniform_decay (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ,
      |ξ| ^ n * ‖gmTraceFourier cutoff t ξ‖ ≤
        C * (1 + |t|) ^ n := by
  choose D hD hDbound using fun p : ℕ =>
    gmTraceKernel_uniform_iteratedFDeriv cutoff p
  let C : ℝ := 2 ^ n * ∑ p ∈ Finset.range (n + 1), D p
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun p _ => hD p)
  refine ⟨C, hC, ?_⟩
  intro t ξ
  have hIntegrable : ∀ (k p : ℕ), k ≤ (0 : ℕ∞) → p ≤ (⊤ : ℕ∞) →
      Integrable (fun x : ℝ =>
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖) := by
    intro k p _hk _hp
    simpa only [gmTraceKernelSchwartz_apply] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (gmTraceKernelSchwartz cutoff t) k p)
  have hFourier := pow_mul_norm_iteratedFDeriv_fourier_le
    (f := gmTraceKernel cutoff t)
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    (contDiff_gmTraceKernel cutoff t) hIntegrable
    (k := 0) (n := n) (by norm_num) (by simp) ξ
  simp only [pow_zero, one_mul, zero_add, Finset.range_one,
    norm_iteratedFDeriv_zero] at hFourier
  have hFourier' : |ξ| ^ n * ‖gmTraceFourier cutoff t ξ‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖ := by
    simpa [gmTraceFourier, Real.norm_eq_abs, SchwartzMap.fourier_coe]
      using hFourier
  calc
    |ξ| ^ n * ‖gmTraceFourier cutoff t ξ‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        D p * (1 + |t|) ^ n := by
      gcongr with p hp
      have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have hint := integral_norm_iteratedFDeriv_gmTraceKernel_le
        cutoff p (hDbound p) t
      calc
        (∫ x : ℝ, ‖iteratedFDeriv ℝ p (gmTraceKernel cutoff t) x‖) ≤
            D p * (1 + |t|) ^ p := hint
        _ ≤ D p * (1 + |t|) ^ n := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by nlinarith [abs_nonneg t]) hpn) (hD p)
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [← Finset.sum_mul]
      ring

/-- Explicit source-strength far-frequency consequence of uniform decay.
Once the Fourier frequency exceeds `(1+|t|)T`, every coefficient has a
`T⁻¹⁰⁰` bound with a constant independent of `t`, `T`, and the frequency. -/
theorem gmTraceFourier_far_frequency_decay (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T t ξ : ℝ}, 1 ≤ T →
      (1 + |t|) * T ≤ |ξ| →
        ‖gmTraceFourier cutoff t ξ‖ ≤ C / T ^ 100 := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_uniform_decay cutoff 101
  refine ⟨C, hC, ?_⟩
  intro T t ξ hT hξ
  have hbasePos : 0 < 1 + |t| := by positivity
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hξPos : 0 < |ξ| := (mul_pos hbasePos hTPos).trans_le hξ
  have hpowξ : ((1 + |t|) * T) ^ 101 ≤ |ξ| ^ 101 :=
    pow_le_pow_left₀ (mul_nonneg hbasePos.le hTPos.le) hξ 101
  have hdiv : ‖gmTraceFourier cutoff t ξ‖ ≤
      C * (1 + |t|) ^ 101 / |ξ| ^ 101 := by
    rw [le_div_iff₀ (pow_pos hξPos 101)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hDecay t ξ
  calc
    ‖gmTraceFourier cutoff t ξ‖ ≤
        C * (1 + |t|) ^ 101 / |ξ| ^ 101 := hdiv
    _ ≤ C * (1 + |t|) ^ 101 / (((1 + |t|) * T) ^ 101) := by
      exact div_le_div_of_nonneg_left (mul_nonneg hC (by positivity))
        (pow_pos (mul_pos hbasePos hTPos) 101) hpowξ
    _ = C / T ^ 101 := by
      rw [mul_pow]
      field_simp [hbasePos.ne', hTPos.ne']
    _ ≤ C / T ^ 100 := by
      exact div_le_div_of_nonneg_left hC (pow_pos hTPos 100)
        (pow_le_pow_right₀ hT (by norm_num : 100 ≤ 101))

/-- Reversing the Fourier frequency is complex conjugation together with
reversal of the Mellin ordinate.  This supplies the negative-frequency half
of the smooth-reflection expansion from the positive-frequency formula. -/
theorem gmTraceFourier_neg_eq_conj (cutoff : GMSmoothCutoff) (t ξ : ℝ) :
    gmTraceFourier cutoff t (-ξ) =
      star (gmTraceFourier cutoff (-t) ξ) := by
  rw [gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq',
    gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  let f : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * I) •
      gmTraceKernelSchwartz cutoff (-t) x
  have hConj : (∫ x : ℝ, star (f x)) = star (∫ x : ℝ, f x) := by
    simpa only using (integral_conj (f := f))
  rw [← hConj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  simp only [Real.inner_apply, gmTraceKernelSchwartz_apply, Complex.star_def,
    smul_eq_mul]
  unfold gmTraceKernel
  rw [map_mul, map_mul, map_pow, conj_ofReal, ← Complex.exp_conj,
    ← Complex.exp_conj]
  push_cast
  ring_nf
  simp only [map_neg, map_mul, map_ofNat, conj_ofReal, conj_I]
  ring_nf

private noncomputable def gmCutoffMellin
    (cutoff : GMSmoothCutoff) (r : ℝ) : ℂ :=
  mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))
    ((1 : ℂ) + (r : ℂ) * I)

private theorem gmCutoffMellin_eq_fourier
    (cutoff : GMSmoothCutoff) (r : ℝ) :
    gmCutoffMellin cutoff r =
      𝓕 (gmMellinKernelSchwartz cutoff) (r / (2 * Real.pi)) := by
  unfold gmCutoffMellin
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (r / (2 * Real.pi)))
  funext u
  rw [gmMellinKernelSchwartz_apply]
  simp [gmMellinKernel, Complex.ofReal_exp]

private theorem continuous_gmCutoffMellin (cutoff : GMSmoothCutoff) :
    Continuous (gmCutoffMellin cutoff) := by
  have hEq : gmCutoffMellin cutoff = fun r : ℝ =>
      𝓕 (gmMellinKernelSchwartz cutoff) (r / (2 * Real.pi)) := by
    funext r
    exact gmCutoffMellin_eq_fourier cutoff r
  rw [hEq]
  exact (𝓕 (gmMellinKernelSchwartz cutoff)).continuous.comp
    (continuous_id.div_const (2 * Real.pi))

private noncomputable def gmMellinReflectionIntegrand
    (cutoff : GMSmoothCutoff) (t q : ℝ) (v r : ℝ) : ℂ :=
  (v / q : ℂ)⁻¹ *
    Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I)) *
      gmCutoffMellin cutoff r *
        Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

private theorem integrable_gmMellinReflectionIntegrand
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (Function.uncurry
      (gmMellinReflectionIntegrand cutoff t (N * m)))
      ((volume.restrict (Set.uIoc (N : ℝ) (2 * N * M))).prod volume) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hH : Integrable (gmCutoffMellin cutoff) := by
    simpa only [gmCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_mellin_gmCutoffSq_one cutoff
  have hConst : Integrable
      (fun _v : ℝ => (m : ℝ))
      (volume.restrict (Set.uIoc (N : ℝ) (2 * N * M))) := by
    exact MeasureTheory.integrableOn_const (hs := by simp)
  have hDom := hConst.mul_prod hH.norm
  apply hDom.mono'
  · have hElementary : AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (z.1 / (N * m) : ℂ)⁻¹ *
            Complex.exp (-(((z.2 * Real.log (z.1 / (N * m)) : ℝ) : ℂ) * I)) *
              Complex.exp ((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))
        ((volume.restrict (Set.uIoc (N : ℝ) (2 * N * M))).prod volume) := by
      exact (by measurability : StronglyMeasurable fun z : ℝ × ℝ =>
        (z.1 / (N * m) : ℂ)⁻¹ *
          Complex.exp (-(((z.2 * Real.log (z.1 / (N * m)) : ℝ) : ℂ) * I)) *
            Complex.exp ((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))
        |>.aestronglyMeasurable
    exact (hElementary.mul (hH.aestronglyMeasurable.comp_snd)).congr
      (Filter.Eventually.of_forall fun z => by
        simp [gmMellinReflectionIntegrand, Function.uncurry_def]
        ring)
  · rw [Measure.ae_prod_iff_ae_ae (by
      apply measurableSet_le
      · have hHM : Measurable fun z : ℝ × ℝ => gmCutoffMellin cutoff z.2 :=
          (continuous_gmCutoffMellin cutoff).measurable.comp measurable_snd
        unfold gmMellinReflectionIntegrand Function.uncurry
        measurability
      · exact ((continuous_gmCutoffMellin cutoff).norm.comp continuous_snd
          |>.const_mul (m : ℝ)).measurable)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with v hv
    filter_upwards with r
    let z : ℝ × ℝ := (v, r)
    have hvIoc : v ∈ Set.Ioc (N : ℝ) (2 * N * M) := by
      simpa only [Set.uIoc_of_le hAB] using hv
    have hvLower : (N : ℝ) ≤ z.1 := by
      simpa only [z] using hvIoc.1.le
    have hvPos : 0 < z.1 := (by exact_mod_cast hN : (0 : ℝ) < N).trans_le hvLower
    rw [show ‖Function.uncurry
        (gmMellinReflectionIntegrand cutoff t (N * m)) z‖ =
        ((N * m : ℝ) / z.1) * ‖gmCutoffMellin cutoff z.2‖ by
      unfold gmMellinReflectionIntegrand Function.uncurry
      simp only [norm_mul, norm_inv]
      simp [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hvPos, inv_div]]
    have hratio : (N * m : ℝ) / z.1 ≤ m := by
      rw [div_le_iff₀ hvPos]
      have hmReal : (0 : ℝ) ≤ m := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- Mellin inversion on the source line `Re s = 1`, expanded as the literal
vertical integral used in Guth--Maynard Lemma 6.2. -/
theorem gmCutoffSq_eq_verticalMellinIntegral (cutoff : GMSmoothCutoff)
    {x : ℝ} (hx : 0 < x) :
    (cutoff x : ℂ) ^ 2 =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + (r : ℂ) * I)) *
            mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))
              ((1 : ℂ) + (r : ℂ) * I) := by
  rw [← gmCutoffSq_mellinInversion cutoff hx]
  unfold mellinInv
  simp only [smul_eq_mul]
  norm_num

/-- The common logarithmic oscillatory integral after the source change of
variables `v = m N u`. -/
noncomputable def gmReflectionIntegral (tau A B : ℝ) : ℂ :=
  ∫ v in A..B,
    (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

private theorem gmCutoffPhase_eq_mellinIntegral
    (cutoff : GMSmoothCutoff) (t q : ℝ) {v : ℝ}
    (hv : 0 < v) (hq : 0 < q) :
    (cutoff (v / q) : ℂ) ^ 2 *
        Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t q v r := by
  have hratio : 0 < v / q := div_pos hv hq
  rw [gmCutoffSq_eq_verticalMellinIntegral cutoff hratio]
  rw [smul_mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  funext r
  unfold gmMellinReflectionIntegrand gmCutoffMellin
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have hExpLog : Complex.exp ((Real.log (v / q) : ℝ) : ℂ) = (v / q : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hratio]
  have hRatioInv : (((v / q : ℝ) : ℂ))⁻¹ = (q : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hRatioInvC : ((v : ℂ) / (q : ℂ))⁻¹ = (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hsplit :
      (Real.log (v / q) : ℂ) * -((1 : ℂ) + (r : ℂ) * I) =
        -(Real.log (v / q) : ℂ) +
          -(((r * Real.log (v / q) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_neg, hExpLog]
  rw [hRatioInv]
  rw [hRatioInvC]

/-- Exact Mellin-reflection identity for the cutoff-weighted common
interval.  This is the Fubini step in Guth--Maynard Lemma 6.2. -/
theorem gmRescaledCutoffIntegral_eq_mellinReflection
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        (cutoff (v / (N * m)) : ℂ) ^ 2 *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ((N * m : ℕ) : ℂ) *
            ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                gmReflectionIntegral (t - r) N (2 * N * M) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hqNat : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hqReal : (0 : ℝ) < N * m := by exact_mod_cast hqNat
  calc
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        (cutoff (v / (N * m)) : ℂ) ^ 2 *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
      ∫ v in (N : ℝ)..(2 * N * M : ℝ),
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t (N * m) v r := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hvPos : 0 < v := hNReal.trans_le
          ((Set.uIcc_of_le hAB ▸ hv).1)
        exact gmCutoffPhase_eq_mellinIntegral cutoff t (N * m) hvPos hqReal
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ v in (N : ℝ)..(2 * N * M : ℝ),
          ∫ r : ℝ, gmMellinReflectionIntegrand cutoff t (N * m) v r := by
        rw [intervalIntegral.integral_smul]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, ∫ v in (N : ℝ)..(2 * N * M : ℝ),
          gmMellinReflectionIntegrand cutoff t (N * m) v r := by
        rw [MeasureTheory.intervalIntegral_integral_swap
          (integrable_gmMellinReflectionIntegrand cutoff t hN hm hmM)]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ((N * m : ℕ) : ℂ) *
            ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                gmReflectionIntegral (t - r) N (2 * N * M) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        unfold gmReflectionIntegral
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v hv
        have hvPos : 0 < v := hNReal.trans_le
          ((Set.uIcc_of_le hAB ▸ hv).1)
        unfold gmMellinReflectionIntegrand
        change
          ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ *
                Complex.exp (-(((r * Real.log (v / ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
            ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
              gmCutoffMellin cutoff r *
                ((v : ℂ)⁻¹ * Complex.exp
                  (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
        have hlog : Real.log (v / ((N : ℝ) * m)) =
            Real.log v - Real.log ((N : ℝ) * m) :=
          Real.log_div hvPos.ne' hqReal.ne'
        rw [hlog]
        have hqComplex : (((N : ℝ) * m : ℝ) : ℂ) = ((N * m : ℕ) : ℂ) := by
          norm_num
        rw [← hqComplex]
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqReal.ne')]
        rw [← Complex.ofReal_log hqReal.le]
        have hRatioInv :
            ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ =
              (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ := by
          field_simp [Complex.ofReal_ne_zero.mpr hqReal.ne',
            Complex.ofReal_ne_zero.mpr hvPos.ne']
        have hExpEq :
            Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
              Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
                Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [hRatioInv]
        calc
          (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ *
                Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
            (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
              (Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
                Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring
          _ = (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
              (Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
                Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
            rw [hExpEq]
          _ = (((N : ℝ) * m : ℝ) : ℂ) *
                Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
              gmCutoffMellin cutoff r *
                ((v : ℂ)⁻¹ * Complex.exp
                  (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring

/-- The unit-modulus primitive used for integration by parts away from the
stationary point. -/
noncomputable def gmReflectionPrimitive (tau v : ℝ) : ℂ :=
  I⁻¹ * Complex.exp
    ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

/-- The quotient of the reflection amplitude by the derivative of its phase.
The only pole is the stationary point `tau/(2π)`. -/
noncomputable def gmReflectionRatio (tau v : ℝ) : ℂ :=
  ((tau - 2 * Real.pi * v : ℝ) : ℂ)⁻¹

/-- Real form of the integration-by-parts quotient. -/
noncomputable def gmReflectionRatioReal (tau v : ℝ) : ℝ :=
  (tau - 2 * Real.pi * v)⁻¹

theorem hasDerivAt_gmReflectionPrimitive {tau v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (gmReflectionPrimitive tau)
      (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
        Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v := by
  have hReal : HasDerivAt
      (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x)
      (tau / v - 2 * Real.pi) v := by
    convert (Real.hasDerivAt_log hv).const_mul tau |>.sub
      ((hasDerivAt_id v).const_mul (2 * Real.pi)) using 1
    simp only [div_eq_mul_inv, mul_one]
  have hExp := (hReal.ofReal_comp.mul_const I).cexp.const_mul I⁻¹
  change HasDerivAt (gmReflectionPrimitive tau) _ v
  convert hExp using 1
  dsimp only [gmReflectionPrimitive]
  field_simp [Complex.I_ne_zero]

theorem hasDerivAt_gmReflectionRatio {tau v : ℝ}
    (hv : tau - 2 * Real.pi * v ≠ 0) :
    HasDerivAt (gmReflectionRatio tau)
      (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v := by
  have hLinear : HasDerivAt
      (fun x : ℝ => tau - 2 * Real.pi * x) (-2 * Real.pi) v := by
    convert (hasDerivAt_id v).const_mul (2 * Real.pi) |>.const_sub tau using 1
    ring
  have hInv := (hLinear.inv hv).ofReal_comp
  change HasDerivAt (gmReflectionRatio tau) _ v
  convert hInv using 1
  · funext x
    simp [gmReflectionRatio]
  · push_cast
    field_simp

theorem hasDerivAt_gmReflectionRatioReal {tau v : ℝ}
    (hv : tau - 2 * Real.pi * v ≠ 0) :
    HasDerivAt (gmReflectionRatioReal tau)
      (2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) v := by
  have hLinear : HasDerivAt
      (fun x : ℝ => tau - 2 * Real.pi * x) (-2 * Real.pi) v := by
    convert (hasDerivAt_id v).const_mul (2 * Real.pi) |>.const_sub tau using 1
    ring
  change HasDerivAt (fun x : ℝ => (tau - 2 * Real.pi * x)⁻¹) _ v
  convert hLinear.inv hv using 1
  field_simp

/-- Pointwise factorization of the reflection integrand as a smooth quotient
times the derivative of a unit-modulus primitive. -/
theorem gmReflectionRatio_mul_primitiveDeriv {tau v : ℝ}
    (hv : v ≠ 0) (hstat : tau - 2 * Real.pi * v ≠ 0) :
    gmReflectionRatio tau v *
        (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
          Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
      (v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
  unfold gmReflectionRatio
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  have hstatC : ((tau - 2 * Real.pi * v : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hstat
  have hDerivative : ((tau / v - 2 * Real.pi : ℝ) : ℂ) =
      ((tau - 2 * Real.pi * v : ℝ) : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [hvC]
  rw [hDerivative]
  field_simp [hstatC]

/-- Exact integration-by-parts identity on an interval which does not meet
the stationary point. -/
theorem gmReflectionIntegral_eq_parts {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a)
    (hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0) :
    gmReflectionIntegral tau a b =
      gmReflectionRatio tau b * gmReflectionPrimitive tau b -
        gmReflectionRatio tau a * gmReflectionPrimitive tau a -
          ∫ v in a..b,
            ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v := by
  have hpos : ∀ v ∈ Set.Icc a b, 0 < v := fun v hv => ha.trans_le hv.1
  have hRatioDeriv : ∀ v ∈ Set.Icc a b,
      HasDerivAt (gmReflectionRatio tau)
        (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v :=
    fun v hv => hasDerivAt_gmReflectionRatio (hstat v hv)
  have hPrimitiveDeriv : ∀ v ∈ Set.Icc a b,
      HasDerivAt (gmReflectionPrimitive tau)
        (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
          Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v :=
    fun v hv => hasDerivAt_gmReflectionPrimitive (hpos v hv).ne'
  have hRatioDerivU : ∀ v ∈ Set.uIcc a b,
      HasDerivAt (gmReflectionRatio tau)
        (((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) v := by
    simpa only [uIcc_of_le hab] using hRatioDeriv
  have hPrimitiveDerivU : ∀ v ∈ Set.uIcc a b,
      HasDerivAt (gmReflectionPrimitive tau)
        (((tau / v - 2 * Real.pi : ℝ) : ℂ) *
          Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) v := by
    simpa only [uIcc_of_le hab] using hPrimitiveDeriv
  have hRatioInt : IntervalIntegrable
      (fun v : ℝ => ((2 * Real.pi /
        (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) volume a b :=
    (continuousOn_of_forall_continuousAt fun v hv => by
      have hvIcc : v ∈ Set.Icc a b := by simpa only [uIcc_of_le hab] using hv
      have hden : tau - 2 * Real.pi * v ≠ 0 := hstat v hvIcc
      exact Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div
          ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
          (pow_ne_zero 2 hden))).intervalIntegrable
  have hPrimitiveInt : IntervalIntegrable
      (fun v : ℝ => ((tau / v - 2 * Real.pi : ℝ) : ℂ) *
        Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) volume a b :=
    (continuousOn_of_forall_continuousAt fun v hv => by
      have hvIcc : v ∈ Set.Icc a b := by simpa only [uIcc_of_le hab] using hv
      have hvNe : v ≠ 0 := (hpos v hvIcc).ne'
      have hFirst : ContinuousAt (fun x : ℝ => tau / x - 2 * Real.pi) v :=
        continuousAt_const.div continuousAt_id hvNe |>.sub continuousAt_const
      have hPhase : ContinuousAt
          (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
        (continuousAt_const.mul (Real.continuousAt_log hvNe)).sub
          (continuousAt_const.mul continuousAt_id)
      exact (Complex.continuous_ofReal.continuousAt.comp hFirst).mul
        ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
          continuousAt_const).cexp).intervalIntegrable
  have hParts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hRatioDerivU hPrimitiveDerivU hRatioInt hPrimitiveInt
  unfold gmReflectionIntegral
  rw [← hParts]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hv
  exact (gmReflectionRatio_mul_primitiveDeriv (hpos v hvIcc).ne'
    (hstat v hvIcc)).symm

theorem norm_gmReflectionPrimitive (tau v : ℝ) :
    ‖gmReflectionPrimitive tau v‖ = 1 := by
  simp [gmReflectionPrimitive, Complex.norm_exp]

theorem norm_gmReflectionRatio (tau v : ℝ) :
    ‖gmReflectionRatio tau v‖ = |tau - 2 * Real.pi * v|⁻¹ := by
  rw [gmReflectionRatio, norm_inv, Complex.norm_real]
  rw [Real.norm_eq_abs]

/-- On the positive axis, the rescaled reflection integrand has norm `1/v`.
This is the amplitude estimate used both near and away from its stationary
point. -/
theorem norm_gmReflectionIntegrand {tau v : ℝ} (hv : 0 < v) :
    ‖(v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))‖ = v⁻¹ := by
  rw [norm_mul, norm_inv]
  simp [Real.norm_eq_abs, abs_of_pos hv, Complex.norm_exp]

/-- Quantitative integration-by-parts bound on an interval avoiding the
stationary point.  The last term is the exact total variation of the phase
quotient. -/
theorem norm_gmReflectionIntegral_le_endpoint_variation {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a)
    (hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0) :
    ‖gmReflectionIntegral tau a b‖ ≤
      |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
        |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
  rw [gmReflectionIntegral_eq_parts hab ha hstat]
  have hDerivU : ∀ v ∈ Set.uIcc a b,
      HasDerivAt (gmReflectionRatioReal tau)
        (2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) v := by
    intro v hv
    apply hasDerivAt_gmReflectionRatioReal
    apply hstat v
    simpa only [uIcc_of_le hab] using hv
  have hDerivContinuous : ContinuousOn
      (fun v : ℝ => 2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2)
      (Set.uIcc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro v hv
    have hvIcc : v ∈ Set.Icc a b := by simpa only [uIcc_of_le hab] using hv
    exact continuousAt_const.div
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
      (pow_ne_zero 2 (hstat v hvIcc))
  have hDerivativeIntegral :
      (∫ v in a..b, 2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2) =
        gmReflectionRatioReal tau b - gmReflectionRatioReal tau a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hDerivU
      hDerivContinuous.intervalIntegrable
  have hVariation :
      ‖∫ v in a..b,
          ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
            gmReflectionPrimitive tau v‖ ≤
        |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
    have hNormIntegralEq :
        (∫ v in a..b,
            ‖((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v‖) =
          ∫ v in a..b, 2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v hv
      change ‖((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
          gmReflectionPrimitive tau v‖ =
        2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2
      rw [norm_mul, norm_gmReflectionPrimitive, mul_one, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (by positivity) (sq_nonneg _)
    calc
      ‖∫ v in a..b,
          ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
            gmReflectionPrimitive tau v‖ ≤
          |∫ v in a..b,
            ‖((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ = |∫ v in a..b,
          2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2| := by
        rw [hNormIntegralEq]
      _ = |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
        rw [hDerivativeIntegral]
  calc
    ‖gmReflectionRatio tau b * gmReflectionPrimitive tau b -
        gmReflectionRatio tau a * gmReflectionPrimitive tau a -
          ∫ v in a..b,
            ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
              gmReflectionPrimitive tau v‖ ≤
        ‖gmReflectionRatio tau b * gmReflectionPrimitive tau b -
          gmReflectionRatio tau a * gmReflectionPrimitive tau a‖ +
            ‖∫ v in a..b,
              ((2 * Real.pi / (tau - 2 * Real.pi * v) ^ 2 : ℝ) : ℂ) *
                gmReflectionPrimitive tau v‖ := norm_sub_le _ _
    _ ≤ (‖gmReflectionRatio tau b * gmReflectionPrimitive tau b‖ +
          ‖gmReflectionRatio tau a * gmReflectionPrimitive tau a‖) +
            |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| :=
      add_le_add (norm_sub_le _ _) hVariation
    _ = |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
          |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := by
      rw [norm_mul, norm_mul, norm_gmReflectionRatio, norm_gmReflectionRatio,
        norm_gmReflectionPrimitive, norm_gmReflectionPrimitive, mul_one, mul_one]

/-- First-derivative bound on an interval strictly to the left of the
stationary point. -/
theorem norm_gmReflectionIntegral_le_left {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hleft : 2 * Real.pi * b < tau) :
    ‖gmReflectionIntegral tau a b‖ ≤ 2 / (tau - 2 * Real.pi * b) := by
  have hdb : 0 < tau - 2 * Real.pi * b := by linarith
  have hda : 0 < tau - 2 * Real.pi * a := by
    have := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0 := by
    intro v hv
    have := mul_le_mul_of_nonneg_left hv.2 (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hBase := norm_gmReflectionIntegral_le_endpoint_variation hab ha hstat
  have hInvOrder : (tau - 2 * Real.pi * a)⁻¹ ≤
      (tau - 2 * Real.pi * b)⁻¹ := by
    apply (inv_le_inv₀ hda hdb).2
    have := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hDiff : 0 ≤ gmReflectionRatioReal tau b - gmReflectionRatioReal tau a := by
    simpa only [gmReflectionRatioReal] using sub_nonneg.mpr hInvOrder
  calc
    ‖gmReflectionIntegral tau a b‖ ≤
        |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
          |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := hBase
    _ = 2 / (tau - 2 * Real.pi * b) := by
      rw [abs_of_pos hdb, abs_of_pos hda, abs_of_nonneg hDiff]
      unfold gmReflectionRatioReal
      ring

/-- First-derivative bound on an interval strictly to the right of the
stationary point. -/
theorem norm_gmReflectionIntegral_le_right {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hright : tau < 2 * Real.pi * a) :
    ‖gmReflectionIntegral tau a b‖ ≤ 2 / (2 * Real.pi * a - tau) := by
  have hda : tau - 2 * Real.pi * a < 0 := by linarith
  have hdb : tau - 2 * Real.pi * b < 0 := by
    have := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hstat : ∀ v ∈ Set.Icc a b, tau - 2 * Real.pi * v ≠ 0 := by
    intro v hv
    have := mul_le_mul_of_nonneg_left hv.1 (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hBase := norm_gmReflectionIntegral_le_endpoint_variation hab ha hstat
  have hInvOrder : (tau - 2 * Real.pi * a)⁻¹ ≤
      (tau - 2 * Real.pi * b)⁻¹ := by
    apply (inv_le_inv_of_neg hda hdb).2
    have := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 2 * Real.pi)
    linarith
  have hDiff : 0 ≤ gmReflectionRatioReal tau b - gmReflectionRatioReal tau a := by
    simpa only [gmReflectionRatioReal] using sub_nonneg.mpr hInvOrder
  calc
    ‖gmReflectionIntegral tau a b‖ ≤
        |tau - 2 * Real.pi * b|⁻¹ + |tau - 2 * Real.pi * a|⁻¹ +
          |gmReflectionRatioReal tau b - gmReflectionRatioReal tau a| := hBase
    _ = 2 / (2 * Real.pi * a - tau) := by
      rw [abs_of_neg hdb, abs_of_neg hda, abs_of_nonneg hDiff]
      unfold gmReflectionRatioReal
      have hNegInv : (tau - 2 * Real.pi * a)⁻¹ =
          -(2 * Real.pi * a - tau)⁻¹ := by
        rw [show tau - 2 * Real.pi * a = -(2 * Real.pi * a - tau) by ring,
          inv_neg]
      have hNegInvB : (tau - 2 * Real.pi * b)⁻¹ =
          -(2 * Real.pi * b - tau)⁻¹ := by
        rw [show tau - 2 * Real.pi * b = -(2 * Real.pi * b - tau) by ring,
          inv_neg]
      rw [hNegInv, hNegInvB]
      ring

/-- Trivial amplitude bound on a positive interval. -/
theorem norm_gmReflectionIntegral_le_length_div {tau a b L : ℝ}
    (hab : a ≤ b) (hL : 0 < L) (hLa : L ≤ a) :
    ‖gmReflectionIntegral tau a b‖ ≤ (b - a) / L := by
  unfold gmReflectionIntegral
  have hBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := L⁻¹)
    (f := fun v : ℝ => (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
    (fun v hv => by
      rw [uIoc_of_le hab] at hv
      have hLv : L ≤ v := hLa.trans (le_of_lt hv.1)
      have hvPos : 0 < v := hL.trans_le hLv
      rw [norm_gmReflectionIntegrand hvPos]
      exact (inv_le_inv₀ hvPos hL).2 hLv)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hBound
  calc
    ‖∫ v in a..b,
        (v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))‖ ≤
        L⁻¹ * (b - a) := hBound
    _ = (b - a) / L := by ring

theorem intervalIntegrable_gmReflectionIntegrand {tau a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable
      (fun v : ℝ => (v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro v hv
  have hvIcc : v ∈ Set.Icc a b := by simpa only [uIcc_of_le hab] using hv
  have hvPos : 0 < v := ha.trans_le hvIcc.1
  have hPhase : ContinuousAt
      (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
    (continuousAt_const.mul (Real.continuousAt_log hvPos.ne')).sub
      (continuousAt_const.mul continuousAt_id)
  exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
      (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
    ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul continuousAt_const).cexp

/-- Pointwise identification of the inner Fubini integral used in the Mellin
reflection formula.  Naming this equality is essential for retaining the
finite Dirichlet polynomial inside the outer Mellin integral. -/
private theorem intervalIntegral_gmMellinReflectionIntegrand_eq
    (cutoff : GMSmoothCutoff) (t r : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ v in (N : ℝ)..(2 * N * M : ℝ),
        gmMellinReflectionIntegrand cutoff t (N * m) v r) =
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hqNat : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hqReal : (0 : ℝ) < N * m := by exact_mod_cast hqNat
  unfold gmReflectionIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvPos : 0 < v := hNReal.trans_le
    ((Set.uIcc_of_le hAB ▸ hv).1)
  unfold gmMellinReflectionIntegrand
  change
    ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ *
          Complex.exp (-(((r * Real.log (v / ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
        gmCutoffMellin cutoff r *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          ((v : ℂ)⁻¹ * Complex.exp
            (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
  have hlog : Real.log (v / ((N : ℝ) * m)) =
      Real.log v - Real.log ((N : ℝ) * m) :=
    Real.log_div hvPos.ne' hqReal.ne'
  rw [hlog]
  have hqComplex : (((N : ℝ) * m : ℝ) : ℂ) = ((N * m : ℕ) : ℂ) := by
    norm_num
  rw [← hqComplex]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqReal.ne')]
  rw [← Complex.ofReal_log hqReal.le]
  have hRatioInv :
      ((v : ℂ) / (((N : ℝ) * m : ℝ) : ℂ))⁻¹ =
        (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hqReal.ne',
      Complex.ofReal_ne_zero.mpr hvPos.ne']
  have hExpEq :
      Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
        Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
          Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hRatioInv]
  calc
    (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ *
          Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
        gmCutoffMellin cutoff r *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) =
      (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
        (Complex.exp (-(((r * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I)) *
          Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring
    _ = (((N : ℝ) * m : ℝ) : ℂ) * (v : ℂ)⁻¹ * gmCutoffMellin cutoff r *
        (Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
          Complex.exp (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
      rw [hExpEq]
    _ = (((N : ℝ) * m : ℝ) : ℂ) *
          Complex.exp ((Real.log ((N : ℝ) * m) : ℂ) * ((r : ℂ) * I)) *
        gmCutoffMellin cutoff r *
          ((v : ℂ)⁻¹ * Complex.exp
            (((((t - r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by ring

/-- Uniform first/second-derivative estimate for the common reflection
integral.  This is the `T₀⁻¹/²` analytic core of Guth--Maynard Lemma 6.2. -/
theorem norm_gmReflectionIntegral_le_ten_div_sqrt {tau A B : ℝ}
    (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖gmReflectionIntegral tau A B‖ ≤ 10 / Real.sqrt tau := by
  let x0 : ℝ := tau / (2 * Real.pi)
  let delta : ℝ := Real.sqrt tau / (4 * Real.pi)
  let L : ℝ := x0 - delta
  let R : ℝ := x0 + delta
  have htauPos : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hsqrtPos : 0 < Real.sqrt tau := Real.sqrt_pos.2 htauPos
  have hsqrtSq : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htauPos.le
  have hsqrtLe : Real.sqrt tau ≤ tau := by
    nlinarith [Real.sqrt_nonneg tau]
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have hLR : L < R := by dsimp only [L, R]; linarith
  have hLFormula : L = (2 * tau - Real.sqrt tau) / (4 * Real.pi) := by
    dsimp only [L, x0, delta]
    field_simp [Real.pi_ne_zero]
    ring
  have hLLower : tau / (4 * Real.pi) ≤ L := by
    rw [hLFormula]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 4 * Real.pi)).2
    linarith
  have hLPos : 0 < L := (div_pos htauPos (by positivity)).trans_le hLLower
  have hLeftDen : tau - 2 * Real.pi * L = Real.sqrt tau / 2 := by
    dsimp only [L, x0, delta]
    field_simp [Real.pi_ne_zero]
    ring
  have hRightDen : 2 * Real.pi * R - tau = Real.sqrt tau / 2 := by
    dsimp only [R, x0, delta]
    field_simp [Real.pi_ne_zero]
    ring
  by_cases hEntireLeft : B ≤ L
  · have hDenPos : 0 < tau - 2 * Real.pi * B := by
      have hScaled := mul_le_mul_of_nonneg_left hEntireLeft
        (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith [hLeftDen, hsqrtPos]
    have hLeft := norm_gmReflectionIntegral_le_left (tau := tau)
      (a := A) (b := B) hAB hA (by linarith)
    calc
      ‖gmReflectionIntegral tau A B‖ ≤ 2 / (tau - 2 * Real.pi * B) := hLeft
      _ ≤ 4 / Real.sqrt tau := by
        have hDen : Real.sqrt tau / 2 ≤ tau - 2 * Real.pi * B := by
          rw [← hLeftDen]
          nlinarith [mul_le_mul_of_nonneg_left hEntireLeft
            (by positivity : 0 ≤ 2 * Real.pi)]
        apply (div_le_div_iff₀ hDenPos hsqrtPos).2
        nlinarith
      _ ≤ 10 / Real.sqrt tau := by
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtPos.le
  by_cases hEntireRight : R ≤ A
  · have hDenPos : 0 < 2 * Real.pi * A - tau := by
      have hScaled := mul_le_mul_of_nonneg_left hEntireRight
        (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith [hRightDen, hsqrtPos]
    have hRight := norm_gmReflectionIntegral_le_right (tau := tau)
      (a := A) (b := B) hAB hA (by linarith)
    calc
      ‖gmReflectionIntegral tau A B‖ ≤ 2 / (2 * Real.pi * A - tau) := hRight
      _ ≤ 4 / Real.sqrt tau := by
        have hDen : Real.sqrt tau / 2 ≤ 2 * Real.pi * A - tau := by
          rw [← hRightDen]
          nlinarith [mul_le_mul_of_nonneg_left hEntireRight
            (by positivity : 0 ≤ 2 * Real.pi)]
        apply (div_le_div_iff₀ hDenPos hsqrtPos).2
        nlinarith
      _ ≤ 10 / Real.sqrt tau := by
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtPos.le
  · have hLB : L < B := lt_of_not_ge hEntireLeft
    have hAR : A < R := lt_of_not_ge hEntireRight
    let l : ℝ := max A L
    let r : ℝ := min B R
    have hAl : A ≤ l := le_max_left _ _
    have hlB : l ≤ B := max_le hAB hLB.le
    have hAr : A ≤ r := le_min hAB hAR.le
    have hrB : r ≤ B := min_le_left _ _
    have hlr : l ≤ r := by
      apply max_le
      · exact hAr
      · exact le_min hLB.le hLR.le
    have hlPos : 0 < l := hA.trans_le hAl
    have hrPos : 0 < r := hlPos.trans_le hlr
    have hLeftPiece : ‖gmReflectionIntegral tau A l‖ ≤
        4 / Real.sqrt tau := by
      by_cases hEq : l = A
      · rw [hEq]
        simp [gmReflectionIntegral]
        positivity
      · have hAL : A < L := by
          have hnot : ¬ L ≤ A := by
            intro hLA
            apply hEq
            exact max_eq_left hLA
          exact lt_of_not_ge hnot
        have hlEq : l = L := max_eq_right hAL.le
        rw [hlEq]
        have hBound := norm_gmReflectionIntegral_le_left hAL.le hA (by
          rw [← sub_pos, hLeftDen]
          positivity)
        rw [hLeftDen] at hBound
        calc
          ‖gmReflectionIntegral tau A L‖ ≤ 2 / (Real.sqrt tau / 2) := hBound
          _ = 4 / Real.sqrt tau := by field_simp; norm_num
    have hRightPiece : ‖gmReflectionIntegral tau r B‖ ≤
        4 / Real.sqrt tau := by
      by_cases hEq : r = B
      · rw [hEq]
        simp [gmReflectionIntegral]
        positivity
      · have hRB : R < B := by
          have hnot : ¬ B ≤ R := by
            intro hBR
            apply hEq
            exact min_eq_left hBR
          exact lt_of_not_ge hnot
        have hrEq : r = R := min_eq_right hRB.le
        rw [hrEq]
        have hBound := norm_gmReflectionIntegral_le_right hRB.le
          (hLPos.trans hLR) (by
          rw [← sub_pos, hRightDen]
          positivity)
        rw [hRightDen] at hBound
        calc
          ‖gmReflectionIntegral tau R B‖ ≤ 2 / (Real.sqrt tau / 2) := hBound
          _ = 4 / Real.sqrt tau := by field_simp; norm_num
    have hMiddlePiece : ‖gmReflectionIntegral tau l r‖ ≤
        2 / Real.sqrt tau := by
      have hTauLowerL : tau / (4 * Real.pi) ≤ l :=
        hLLower.trans (le_max_right _ _)
      have hLength : r - l ≤ Real.sqrt tau / (2 * Real.pi) := by
        have hlL : L ≤ l := le_max_right _ _
        have hrR : r ≤ R := min_le_right _ _
        have hRL : R - L = Real.sqrt tau / (2 * Real.pi) := by
          dsimp only [R, L, delta]
          ring
        linarith
      have hTrivial := norm_gmReflectionIntegral_le_length_div (tau := tau) hlr
        (div_pos htauPos (by positivity : 0 < 4 * Real.pi)) hTauLowerL
      calc
        ‖gmReflectionIntegral tau l r‖ ≤
            (r - l) / (tau / (4 * Real.pi)) := hTrivial
        _ ≤ (Real.sqrt tau / (2 * Real.pi)) /
            (tau / (4 * Real.pi)) := by
          gcongr
        _ = 2 / Real.sqrt tau := by
          field_simp [Real.pi_ne_zero, hsqrtPos.ne', htauPos.ne']
          nlinarith
    have hIntAl := intervalIntegrable_gmReflectionIntegrand (tau := tau) hAl hA
    have hIntlR := intervalIntegrable_gmReflectionIntegrand (tau := tau) hlr hlPos
    have hIntrB := intervalIntegrable_gmReflectionIntegrand (tau := tau) hrB hrPos
    have hSplit : gmReflectionIntegral tau A B =
        gmReflectionIntegral tau A l + gmReflectionIntegral tau l r +
          gmReflectionIntegral tau r B := by
      unfold gmReflectionIntegral
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntAl
        (hIntlR.trans hIntrB)]
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntlR hIntrB]
      ring
    rw [hSplit]
    calc
      ‖gmReflectionIntegral tau A l + gmReflectionIntegral tau l r +
          gmReflectionIntegral tau r B‖ ≤
          ‖gmReflectionIntegral tau A l‖ + ‖gmReflectionIntegral tau l r‖ +
            ‖gmReflectionIntegral tau r B‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 4 / Real.sqrt tau + 2 / Real.sqrt tau + 4 / Real.sqrt tau := by
        gcongr
      _ = 10 / Real.sqrt tau := by ring

/-- A bounded-variation amplitude may be inserted into the logarithmic
reflection integral without losing the square-root cancellation.  This is
the weighted van der Corput estimate needed by the Type-I B-process: the
coefficient is the bare `10 / sqrt tau` bound multiplied by the endpoint value
and total variation of the amplitude.

The statement is deliberately quantitative.  It does not package a desired
reflection conclusion as a hypothesis; `w'` is the actual derivative of the
concrete amplitude and the right side is its literal interval integral. -/
theorem norm_weighted_gmReflectionIntegral_le
    {tau A B : ℝ} (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B)
    (w w' : ℝ → ℂ)
    (hw : ∀ x ∈ Set.Icc A B, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' volume A B) :
    ‖∫ v in A..B, w v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ ≤
      (10 / Real.sqrt tau) *
        (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by
  let k : ℝ → ℂ := fun v =>
    (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))
  let F : ℝ → ℂ := fun x => ∫ v in A..x, k v
  have hkInt : IntervalIntegrable k volume A B := by
    simpa only [k] using intervalIntegrable_gmReflectionIntegrand hAB hA
  have hkContinuousPos : ContinuousOn k (Set.Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxPos : 0 < x := hx
    have hPhase : ContinuousAt
        (fun y : ℝ => tau * Real.log y - 2 * Real.pi * y) x :=
      (continuousAt_const.mul (Real.continuousAt_log hxPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
    exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
        (Complex.ofReal_ne_zero.mpr hxPos.ne') |>.mul
      ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
        continuousAt_const).cexp
  have hkContinuousAt : ∀ x ∈ Set.Icc A B, ContinuousAt k x := by
    intro x hx
    have hxPos : 0 < x := hA.trans_le hx.1
    exact (hkContinuousPos x hxPos).continuousAt (Ioi_mem_nhds hxPos)
  have hkContinuous : ContinuousOn k (Set.Icc A B) :=
    fun x hx => (hkContinuousAt x hx).continuousWithinAt
  have hFDeriv : ∀ x ∈ Set.Icc A B, HasDerivAt F (k x) x := by
    intro x hx
    have hkAx : IntervalIntegrable k volume A x := by
      simpa only [k] using
        intervalIntegrable_gmReflectionIntegrand hx.1 hA
    exact intervalIntegral.integral_hasDerivAt_right hkAx
      (hkContinuousPos.stronglyMeasurableAtFilter isOpen_Ioi x
        (hA.trans_le hx.1))
      (hkContinuousAt x hx)
  have hFContinuous : ContinuousOn F (Set.Icc A B) :=
    fun x hx => (hFDeriv x hx).continuousAt.continuousWithinAt
  have hFContinuousU : ContinuousOn F (Set.uIcc A B) := by
    simpa only [Set.uIcc_of_le hAB] using hFContinuous
  have hwU : ∀ x ∈ Set.uIcc A B, HasDerivAt w (w' x) x := by
    simpa only [Set.uIcc_of_le hAB] using hw
  have hFDerivU : ∀ x ∈ Set.uIcc A B, HasDerivAt F (k x) x := by
    simpa only [Set.uIcc_of_le hAB] using hFDeriv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hwU hFDerivU hw' hkInt
  have hFA : F A = 0 := by simp [F]
  have hFB : F B = gmReflectionIntegral tau A B := by
    rfl
  have hFBound : ∀ x ∈ Set.Icc A B, ‖F x‖ ≤ 10 / Real.sqrt tau := by
    intro x hx
    simpa only [F, k, gmReflectionIntegral] using
      norm_gmReflectionIntegral_le_ten_div_sqrt htau hA hx.1
  have hvariationNonneg : 0 ≤ ∫ v in A..B, ‖w' v‖ := by
    exact intervalIntegral.integral_nonneg hAB fun _ _ => norm_nonneg _
  have hweightedVariation :
      ‖∫ v in A..B, w' v * F v‖ ≤
        (10 / Real.sqrt tau) * ∫ v in A..B, ‖w' v‖ := by
    calc
      ‖∫ v in A..B, w' v * F v‖ ≤
          |∫ v in A..B, ‖w' v * F v‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ v in A..B, ‖w' v * F v‖ := by
        rw [abs_of_nonneg]
        exact intervalIntegral.integral_nonneg hAB fun _ _ => norm_nonneg _
      _ ≤ ∫ v in A..B, ‖w' v‖ * (10 / Real.sqrt tau) := by
        apply intervalIntegral.integral_mono_on hAB
        · simpa only [norm_mul] using
            (hw'.norm.mul_continuousOn hFContinuousU.norm)
        · exact hw'.norm.mul_const (10 / Real.sqrt tau)
        · intro v hv
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hFBound v hv) (norm_nonneg _)
      _ = (10 / Real.sqrt tau) * ∫ v in A..B, ‖w' v‖ := by
        rw [intervalIntegral.integral_mul_const]
        ring
  rw [hparts, hFA, hFB]
  simp only [mul_zero, sub_zero]
  calc
    ‖w B * gmReflectionIntegral tau A B - ∫ v in A..B, w' v * F v‖ ≤
        ‖w B * gmReflectionIntegral tau A B‖ +
          ‖∫ v in A..B, w' v * F v‖ := norm_sub_le _ _
    _ ≤ ‖w B‖ * (10 / Real.sqrt tau) +
          (10 / Real.sqrt tau) * ∫ v in A..B, ‖w' v‖ := by
      gcongr
      rw [norm_mul]
      gcongr
      exact norm_gmReflectionIntegral_le_ten_div_sqrt htau hA hAB
    _ = (10 / Real.sqrt tau) *
          (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by ring

/-- The real power amplitude occurring after Mellin reflection.  Writing it
as an exponential keeps the derivative and its parameter dependence
literal, including at nonintegral `sigma`. -/
noncomputable def gmReflectionPowerWeight (sigma v : ℝ) : ℂ :=
  Complex.exp (((-sigma * Real.log v : ℝ) : ℂ))

theorem hasDerivAt_gmReflectionPowerWeight
    {sigma v : ℝ} (hv : 0 < v) :
    HasDerivAt (gmReflectionPowerWeight sigma)
      (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v) v := by
  unfold gmReflectionPowerWeight
  have hReal : HasDerivAt (fun x : ℝ => -sigma * Real.log x) (-sigma / v) v := by
    simpa only [div_eq_mul_inv] using
      (Real.hasDerivAt_log hv.ne').const_mul (-sigma)
  convert hReal.ofReal_comp.cexp using 1
  all_goals ring

theorem norm_gmReflectionPowerWeight {sigma v : ℝ} (hv : 0 < v) :
    ‖gmReflectionPowerWeight sigma v‖ = v ^ (-sigma) := by
  unfold gmReflectionPowerWeight
  rw [Complex.norm_exp]
  simp only [ofReal_re]
  rw [Real.rpow_def_of_pos hv]
  congr 1
  ring

/-- Weighted logarithmic B-process estimate for the exact power amplitude.
The variation integral is left visible: downstream scale arithmetic may use
either its exact antiderivative or a sharper restricted-window estimate. -/
theorem norm_powerWeighted_gmReflectionIntegral_le
    {tau sigma A B : ℝ} (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ v in A..B, gmReflectionPowerWeight sigma v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  let w' : ℝ → ℂ := fun v =>
    (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v)
  have hw : ∀ x ∈ Set.Icc A B,
      HasDerivAt (gmReflectionPowerWeight sigma) (w' x) x := by
    intro x hx
    exact hasDerivAt_gmReflectionPowerWeight (hA.trans_le hx.1)
  have hw' : IntervalIntegrable w' volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxIcc : x ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hx
    have hxPos : 0 < x := hA.trans_le hxIcc.1
    exact (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div continuousAt_id hxPos.ne')).mul
      (hasDerivAt_gmReflectionPowerWeight hxPos).continuousAt
  have hBase := norm_weighted_gmReflectionIntegral_le htau hA hAB
    (gmReflectionPowerWeight sigma) w' hw hw'
  simpa only [w', norm_gmReflectionPowerWeight (hA.trans_le hAB)] using hBase

theorem star_gmReflectionPowerWeight (sigma v : ℝ) :
    star (gmReflectionPowerWeight sigma v) =
      gmReflectionPowerWeight sigma v := by
  unfold gmReflectionPowerWeight
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

/-- Conjugated form of the power-weighted B-process estimate.  This is the
Fourier sign produced by the medium Type-I block. -/
theorem norm_conj_powerWeighted_gmReflectionIntegral_le
    {tau sigma A B : ℝ} (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ v in A..B, gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  let f : ℝ → ℂ := fun v =>
    gmReflectionPowerWeight sigma v *
      ((v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
  have hfInt : IntervalIntegrable f volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro v hv
    have hvIcc : v ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans_le hvIcc.1
    have hPhase : ContinuousAt
        (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
      (continuousAt_const.mul (Real.continuousAt_log hvPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
    exact (hasDerivAt_gmReflectionPowerWeight hvPos).continuousAt.mul
      ((Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
          (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
        ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
          continuousAt_const).cexp)
  have hConj := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hfInt
  have hPointwise : (fun v : ℝ => star (f v)) = fun v =>
      gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    funext v
    dsimp only [f]
    rw [Complex.star_def, map_mul]
    have hs := star_gmReflectionPowerWeight sigma v
    rw [Complex.star_def] at hs
    rw [hs]
  have hConj' : (∫ v in A..B, star (f v)) =
      star (∫ v in A..B, f v) := by
    simpa only [Complex.conjCLE_apply, Complex.star_def] using hConj
  rw [← hPointwise, hConj']
  rw [Complex.star_def, Complex.norm_conj]
  exact norm_powerWeighted_gmReflectionIntegral_le htau hA hAB

/-- Positive Fourier modes may be integrated over the common source interval
`[1/m, 2M/m]`.  Its endpoints were chosen so that the support `[1,2]` is
contained in the interval for every `1 ≤ m ≤ M`. -/
theorem gmTraceFourier_pos_eq_interval (cutoff : GMSmoothCutoff)
    (t N : ℝ) {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t (N * m) =
      ∫ u in (1 : ℝ) / m..(2 : ℝ) * M / m,
        Complex.exp (((-2 * Real.pi * (u * (N * m)) : ℝ) : ℂ) * I) *
          gmTraceKernel cutoff t u := by
  rw [gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, gmTraceKernelSchwartz_apply]
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hcut : cutoff u ≠ 0 := by
    intro hzero
    apply hu
    simp [gmTraceKernel, hzero]
  have huRange := cutoff.support hcut
  rw [Set.mem_Ioc]
  constructor
  · have hmPos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hInv : (1 : ℝ) / m ≤ 1 := by
      rw [div_le_one hmPos]
      exact hmOne
    rcases hInv.eq_or_lt with hEq | hLt
    · have hmEq : m = 1 := by
        norm_num [div_eq_iff (ne_of_gt hmPos)] at hEq
        exact_mod_cast hEq
      subst m
      simp only [Nat.cast_one, div_one]
      exact lt_of_le_of_ne huRange.1 fun huEq =>
        hcut (huEq ▸ gmSmoothCutoff_eq_zero_at_one cutoff)
    · exact hLt.trans_le huRange.1
  · have hmPos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hmMReal : (m : ℝ) ≤ M := by exact_mod_cast hmM
    apply huRange.2.trans
    rw [le_div_iff₀ hmPos]
    nlinarith

/-- Exact source rescaling of a positive Fourier coefficient.  The phase
factor `(mN)^(-it)` contains the logarithmic dependence on the mode outside
the common integral `[N,2NM]`; the remaining occurrence of the mode is only
in the smooth cutoff. -/
theorem gmTraceFourier_pos_rescale (cutoff : GMSmoothCutoff)
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ((N * m : ℕ) : ℂ)⁻¹ *
        ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
        ∫ v in (N : ℝ)..(2 * N * M : ℝ),
          (cutoff (v / (N * m)) : ℂ) ^ 2 *
            Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
  rw [gmTraceFourier_pos_eq_interval cutoff t (N : ℝ) hm hmM]
  have hNmNat : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hNm : (0 : ℝ) < N * m := by exact_mod_cast hNmNat
  let f : ℝ → ℂ := fun u =>
    Complex.exp (((-2 * Real.pi * (u * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
      gmTraceKernel cutoff t u
  have hChange := intervalIntegral.integral_comp_div_add
    (f := fun u : ℝ =>
      Complex.exp (((-2 * Real.pi * (u * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
        gmTraceKernel cutoff t u)
    (a := (N : ℝ)) (b := (2 * N * M : ℝ)) hNm.ne' 0
  simp only [add_zero] at hChange
  have hLower : (N : ℝ) / (N * m) = (1 : ℝ) / m := by field_simp
  have hUpper : (2 * N * M : ℝ) / (N * m) = (2 : ℝ) * M / m := by
    field_simp
  rw [hLower, hUpper, Complex.real_smul] at hChange
  have hSolve :
      (∫ u in (1 : ℝ) / m..(2 : ℝ) * M / m,
          Complex.exp (((-2 * Real.pi * (u * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
            gmTraceKernel cutoff t u) =
        (((N * m : ℕ) : ℂ))⁻¹ *
          ∫ v in (N : ℝ)..(2 * N * M : ℝ),
            Complex.exp (((-2 * Real.pi * ((v / ((N : ℝ) * m)) *
              ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
              gmTraceKernel cutoff t (v / ((N : ℝ) * m)) := by
    apply (eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hNmNat.ne')).2
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_natCast,
      Complex.ofReal_mul] using hChange.symm
  have hIntegralFactor :
      (∫ v in (N : ℝ)..(2 * N * M : ℝ),
          Complex.exp (((-2 * Real.pi * ((v / ((N : ℝ) * m)) *
            ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
            gmTraceKernel cutoff t (v / ((N : ℝ) * m))) =
        ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ∫ v in (N : ℝ)..(2 * N * M : ℝ),
            (cutoff (v / (N * m)) : ℂ) ^ 2 *
              Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hvPos : 0 < v := by
      have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
      have hNUpper : (N : ℝ) ≤ 2 * N * M := by
        have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
        nlinarith [mul_nonneg hNReal.le (sub_nonneg.mpr hMReal)]
      exact hNReal.trans_le
        (Set.uIcc_of_le hNUpper ▸ hv).1
    have hNmComplex : ((((N : ℝ) * m : ℝ) : ℂ)) = ((N * m : ℕ) : ℂ) := by
      norm_num
    have hNmComplexNe : ((N * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNmNat.ne'
    unfold gmTraceKernel
    have hLogDiv : Real.log (v / ((N : ℝ) * m)) =
        Real.log v - Real.log ((N : ℝ) * m) := Real.log_div hvPos.ne' hNm.ne'
    have hCpow : ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) =
        Complex.exp (-((t : ℂ) * I) * Complex.log ((N * m : ℕ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hNmComplexNe]
      congr 1
      ring
    have hCancel : v / ((N : ℝ) * m) * ((N : ℝ) * m) = v := by
      exact div_mul_cancel₀ v hNm.ne'
    change
      Complex.exp (((-2 * Real.pi *
          ((v / ((N : ℝ) * m)) * ((N : ℝ) * m)) : ℝ) : ℂ) * I) *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
            Complex.exp ((((t * Real.log (v / ((N : ℝ) * m)) : ℝ) : ℂ) * I))) =
        ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
            Complex.exp ((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))
    rw [hCancel, hCpow, hLogDiv]
    rw [← hNmComplex]
    rw [← Complex.ofReal_log hNm.le]
    let A : ℂ := ((-2 * Real.pi * v : ℝ) : ℂ) * I
    let B : ℂ := ((t * (Real.log v - Real.log ((N : ℝ) * m)) : ℝ) : ℂ) * I
    let C : ℂ := -((t : ℂ) * I) * (Real.log ((N : ℝ) * m) : ℂ)
    let D : ℂ := ((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I
    change Complex.exp A *
        ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp B) =
      Complex.exp C *
        ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp D)
    calc
      Complex.exp A *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp B) =
          (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
            (Complex.exp A * Complex.exp B) := by ring
      _ = (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp (A + B) := by
        rw [Complex.exp_add]
      _ = (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp (C + D) := by
        congr 2
        dsimp only [A, B, C, D]
        push_cast
        ring
      _ = (cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 *
          (Complex.exp C * Complex.exp D) := by rw [Complex.exp_add]
      _ = Complex.exp C *
          ((cutoff (v / ((N : ℝ) * m)) : ℂ) ^ 2 * Complex.exp D) := by ring
  rw [hSolve, hIntegralFactor]
  ring

/-- Exact positive-mode form of Guth--Maynard smooth reflection.  All
dependence on the Fourier mode is outside the common oscillatory integral. -/
theorem gmTraceFourier_pos_eq_mellinReflection (cutoff : GMSmoothCutoff)
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            ((N * m : ℕ) : ℂ) *
              ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
                gmCutoffMellin cutoff r *
                  gmReflectionIntegral (t - r) N (2 * N * M)) := by
  rw [gmTraceFourier_pos_rescale cutoff t hN hm hmM]
  rw [gmRescaledCutoffIntegral_eq_mellinReflection cutoff t hN hm hmM]

/-- The reflected Mellin mode occurring on the right side of the exact
finite approximate functional equation. -/
noncomputable def gmReflectedMode (cutoff : GMSmoothCutoff)
    (t : ℝ) (N m M : ℕ) : ℂ :=
  ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
    ((1 / (2 * Real.pi) : ℝ) •
      ∫ r : ℝ,
        ((N * m : ℕ) : ℂ) *
          ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
            gmCutoffMellin cutoff r *
              gmReflectionIntegral (t - r) N (2 * N * M))

/-- One positive reflected mode before summing over the Fourier frequency.
The normalization is arranged so that the natural-number scale cancels
inside the aggregate sum. -/
noncomputable def gmPositiveDualModeIntegrand (cutoff : GMSmoothCutoff)
    (t : ℝ) (N M m : ℕ) (r : ℝ) : ℂ :=
  ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
    ((1 / (2 * Real.pi) : ℝ) •
      (((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M)))

/-- The common finite Dirichlet polynomial retained inside the Mellin
integral.  This is the cancellation-bearing object missing from a
mode-by-mode triangle inequality. -/
noncomputable def gmPositiveDualDirichletPoly
    (t : ℝ) (N M : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I))

private theorem integrable_gmPositiveDualModeIntegrand
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    Integrable (gmPositiveDualModeIntegrand cutoff t N M m) := by
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hm.trans hmM
    nlinarith
  have hProd := integrable_gmMellinReflectionIntegrand cutoff t hN hm hmM
  have hInner : Integrable (fun r : ℝ =>
      ∫ v in (N : ℝ)..(2 * N * M : ℝ),
        gmMellinReflectionIntegrand cutoff t (N * m) v r) := by
    simpa only [intervalIntegral.integral_of_le hAB, Set.uIoc_of_le hAB,
      Function.uncurry_apply_pair] using
      hProd.integral_prod_right
  have hSimplified : Integrable (fun r : ℝ =>
      ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
        gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M)) := by
    apply hInner.congr
    filter_upwards with r
    exact intervalIntegral_gmMellinReflectionIntegrand_eq
      cutoff t r hN hm hmM
  have hMul := hSimplified.const_mul
    (((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
      ((1 / (2 * Real.pi) : ℝ) : ℂ))
  convert hMul using 1
  funext r
  rw [gmPositiveDualModeIntegrand, Complex.real_smul]
  ring

/-- Each positive Fourier coefficient is the integral of its normalized
dual-mode integrand. -/
theorem gmTraceFourier_pos_eq_integral_dualMode (cutoff : GMSmoothCutoff)
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      ∫ r : ℝ, gmPositiveDualModeIntegrand cutoff t N M m r := by
  rw [gmTraceFourier_pos_eq_mellinReflection cutoff t hN hm hmM]
  unfold gmPositiveDualModeIntegrand
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_smul]

/-- Exact aggregate positive-mode identity with the finite Dirichlet
polynomial kept inside the single Mellin integral. -/
theorem gmTraceFourier_pos_sum_eq_integral_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)) =
      ∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r := by
  calc
    (∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)) =
        ∑ m ∈ Finset.Icc 1 M,
          ∫ r : ℝ, gmPositiveDualModeIntegrand cutoff t N M m r := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmRange := Finset.mem_Icc.mp hm
      exact gmTraceFourier_pos_eq_integral_dualMode cutoff t hN
        hmRange.1 hmRange.2
    _ = ∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r := by
      symm
      apply MeasureTheory.integral_finsetSum
      intro m hm
      have hmRange := Finset.mem_Icc.mp hm
      exact integrable_gmPositiveDualModeIntegrand cutoff t hN
        hmRange.1 hmRange.2

/-- Algebraic cancellation of the scale factors in the aggregate integrand.
The remaining finite sum is precisely one Dirichlet polynomial. -/
theorem sum_gmPositiveDualModeIntegrand_eq
    (cutoff : GMSmoothCutoff) (t r : ℝ) {N M : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r) =
      (1 / (2 * Real.pi) : ℝ) •
        (gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) *
            gmPositiveDualDirichletPoly t N M r) := by
  rw [gmPositiveDualDirichletPoly]
  rw [Complex.real_smul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < N * m := by
    exact Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
  have hq : ((N * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [gmPositiveDualModeIntegrand]
  have hpow :
      ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) =
        ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I)) := by
    rw [← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  simp_rw [Complex.real_smul]
  have hqCancel : ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) = 1 :=
    inv_mul_cancel₀ hq
  calc
    ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
              gmCutoffMellin cutoff r *
                gmReflectionIntegral (t - r) N (2 * N * M))) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ)) *
          (((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
            ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I)) *
          gmCutoffMellin cutoff r *
            gmReflectionIntegral (t - r) N (2 * N * M)) := by ring
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (gmCutoffMellin cutoff r *
          gmReflectionIntegral (t - r) N (2 * N * M) *
            ((N * m : ℕ) : ℂ) ^ ((((r - t : ℝ) : ℂ) * I)))) := by
      rw [hqCancel, hpow]
      ring

/-- Cancellation-preserving norm form of the positive half of Guth--Maynard
Lemma 6.2.  No factor equal to the number of Fourier modes is introduced. -/
theorem norm_gmTraceFourier_pos_sum_le_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    ‖∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)‖ ≤
      ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖ := by
  rw [gmTraceFourier_pos_sum_eq_integral_dualPoly cutoff t hN]
  calc
    ‖∫ r : ℝ, ∑ m ∈ Finset.Icc 1 M,
        gmPositiveDualModeIntegrand cutoff t N M m r‖ ≤
        ∫ r : ℝ, ‖∑ m ∈ Finset.Icc 1 M,
          gmPositiveDualModeIntegrand cutoff t N M m r‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with r
      rw [sum_gmPositiveDualModeIntegrand_eq cutoff t r hN]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity :
        0 < (1 / (2 * Real.pi) : ℝ)), norm_mul, norm_mul]
      ring

/-- The negative Fourier modes satisfy the conjugate cancellation-preserving
bound.  In particular, no factor equal to the number of modes is introduced
on the negative half either. -/
theorem norm_gmTraceFourier_neg_sum_le_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    ‖∑ m ∈ Finset.Icc 1 M,
        gmTraceFourier cutoff t (-((N : ℝ) * m))‖ ≤
      ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖ := by
  have hsum :
      (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff t (-((N : ℝ) * m))) =
        star (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff (-t) ((N : ℝ) * m)) := by
    calc
      (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff t (-((N : ℝ) * m))) =
          ∑ m ∈ Finset.Icc 1 M,
            star (gmTraceFourier cutoff (-t) ((N : ℝ) * m)) := by
        apply Finset.sum_congr rfl
        intro m _
        exact gmTraceFourier_neg_eq_conj cutoff t ((N : ℝ) * m)
      _ = star (∑ m ∈ Finset.Icc 1 M,
          gmTraceFourier cutoff (-t) ((N : ℝ) * m)) := by simp
  rw [hsum, norm_star]
  exact norm_gmTraceFourier_pos_sum_le_dualPoly cutoff (-t) hN

/-- Cancellation-preserving estimate for the complete retained signed window.
This removes the spurious mode-cardinality loss from
`norm_gmSmoothReflection_native_le`.  The uniform `T₀⁻¹ᐟ²` extraction and the
summed omitted-frequency remainder required by the published Lemma 6.2 remain
separate obligations. -/
theorem norm_gmTraceFourier_signed_sum_le_dualPoly
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
      (∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖) +
      ∫ r : ℝ, (1 / (2 * Real.pi) : ℝ) *
        ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖ := by
  rw [Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_gmTraceFourier_pos_sum_le_dualPoly cutoff t hN)
    (norm_gmTraceFourier_neg_sum_le_dualPoly cutoff t hN))

/-- Positive Fourier modes are exactly the reflected Mellin modes. -/
theorem gmTraceFourier_pos_eq_reflectedMode (cutoff : GMSmoothCutoff)
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t ((N : ℝ) * m) =
      gmReflectedMode cutoff t N m M := by
  exact gmTraceFourier_pos_eq_mellinReflection cutoff t hN hm hmM

/-- Exact negative-mode form of smooth reflection.  Together with
`gmTraceFourier_pos_eq_mellinReflection`, this covers every nonzero signed
Poisson mode; no symmetry assumption is left to a downstream theorem. -/
theorem gmTraceFourier_neg_eq_mellinReflection (cutoff : GMSmoothCutoff)
    (t : ℝ) {N m M : ℕ} (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    gmTraceFourier cutoff t (-((N : ℝ) * m)) =
      star (
        ((N * m : ℕ) : ℂ)⁻¹ *
          ((N * m : ℕ) : ℂ) ^ (-(((-t : ℝ) : ℂ) * I)) *
            ((1 / (2 * Real.pi) : ℝ) •
              ∫ r : ℝ,
                ((N * m : ℕ) : ℂ) *
                  ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
                    gmCutoffMellin cutoff r *
                      gmReflectionIntegral (-t - r) N (2 * N * M))) := by
  rw [gmTraceFourier_neg_eq_conj]
  rw [gmTraceFourier_pos_eq_mellinReflection cutoff (-t) hN hm hmM]

/-- Exact finite signed-mode identity used in Guth--Maynard smooth reflection.
Every retained nonzero mode is represented, with the negative half supplied
by proved conjugation symmetry.  This identity is not the quantitative
complete-mode approximate functional equation of Lemma 6.2. -/
theorem gmSmoothReflection_native (cutoff : GMSmoothCutoff)
    (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))) =
      ∑ m ∈ Finset.Icc 1 M,
        (gmReflectedMode cutoff t N m M +
          star (gmReflectedMode cutoff (-t) N m M)) := by
  apply Finset.sum_congr rfl
  intro m hm
  have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hm
  rw [gmTraceFourier_pos_eq_reflectedMode cutoff t hN hmRange.1 hmRange.2,
    gmTraceFourier_neg_eq_conj,
    gmTraceFourier_pos_eq_reflectedMode cutoff (-t) hN hmRange.1 hmRange.2]

/-- Finite positive-frequency dual sum in the exact source range.  Every
mode shares the interval `[N,2NM]`, so this theorem is directly consumable by
the Section 6 Dirichlet-polynomial step. -/
theorem gmTraceFourier_pos_sum_eq_mellinReflection
    (cutoff : GMSmoothCutoff) (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    (∑ m ∈ Finset.Icc 1 M, gmTraceFourier cutoff t ((N : ℝ) * m)) =
      ∑ m ∈ Finset.Icc 1 M,
        ((N * m : ℕ) : ℂ)⁻¹ * ((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
          ((1 / (2 * Real.pi) : ℝ) •
            ∫ r : ℝ,
              ((N * m : ℕ) : ℂ) *
                ((N * m : ℕ) : ℂ) ^ (((r : ℂ) * I)) *
                  gmCutoffMellin cutoff r *
                    gmReflectionIntegral (t - r) N (2 * N * M)) := by
  apply Finset.sum_congr rfl
  intro m hm
  have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hm
  exact gmTraceFourier_pos_eq_mellinReflection cutoff t hN hmRange.1 hmRange.2

/-- Norm form of the smooth-reflection formula.  The mode factors have unit
modulus and the Jacobian cancels exactly, leaving one common Mellin weight
and the common oscillatory integral. -/
theorem norm_gmTraceFourier_pos_le_mellinReflection
    (cutoff : GMSmoothCutoff) (t : ℝ) {N m M : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmM : m ≤ M) :
    ‖gmTraceFourier cutoff t ((N : ℝ) * m)‖ ≤
      (1 / (2 * Real.pi) : ℝ) *
        ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ := by
  rw [gmTraceFourier_pos_eq_mellinReflection cutoff t hN hm hmM]
  have hq : 0 < N * m := Nat.mul_pos hN (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hqC : ((N * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqNorm : ‖((N * m : ℕ) : ℂ)‖ = (N * m : ℝ) := by simp
  have hCpowT : ‖((N * m : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hq]
    simp
  have hCpowR (r : ℝ) : ‖((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hq]
    simp
  rw [norm_mul, norm_mul, norm_inv, hqNorm, hCpowT, mul_one,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    (N * m : ℝ)⁻¹ * ((1 / (2 * Real.pi)) *
        ‖∫ r : ℝ,
          ((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
            gmCutoffMellin cutoff r *
              gmReflectionIntegral (t - r) N (2 * N * M)‖) ≤
      (N * m : ℝ)⁻¹ * ((1 / (2 * Real.pi)) *
        ∫ r : ℝ,
          ‖((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
            gmCutoffMellin cutoff r *
              gmReflectionIntegral (t - r) N (2 * N * M)‖) := by
        gcongr
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = (1 / (2 * Real.pi)) *
        ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ := by
      have hqReal : (0 : ℝ) < N * m := by exact_mod_cast hq
      calc
        (N * m : ℝ)⁻¹ * ((1 / (2 * Real.pi)) *
            ∫ r : ℝ,
              ‖((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
                gmCutoffMellin cutoff r *
                  gmReflectionIntegral (t - r) N (2 * N * M)‖) =
          ∫ r : ℝ, (N * m : ℝ)⁻¹ * (1 / (2 * Real.pi)) *
              ‖((N * m : ℕ) : ℂ) * ((N * m : ℕ) : ℂ) ^ ((r : ℂ) * I) *
                gmCutoffMellin cutoff r *
                  gmReflectionIntegral (t - r) N (2 * N * M)‖ := by
            rw [MeasureTheory.integral_const_mul]
            ring
        _ = ∫ r : ℝ, (1 / (2 * Real.pi)) *
            (‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with r
          rw [norm_mul, norm_mul, norm_mul, hqNorm, hCpowR, mul_one]
          field_simp [hqReal.ne']
        _ = (1 / (2 * Real.pi)) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ := by
          rw [MeasureTheory.integral_const_mul]

/-- Coarse finite signed-mode estimate obtained by the triangle inequality.
It loses the cardinality of the mode set and therefore is not the quantitative
Lemma 6.2 estimate consumed by `S₂`.  The aggregate positive-mode identity
below preserves the cancellation-bearing finite polynomial and is the correct
starting point for that remaining estimate. -/
theorem norm_gmSmoothReflection_native_le (cutoff : GMSmoothCutoff)
    (t : ℝ) {N M : ℕ} (hN : 0 < N) :
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
      ((Finset.Icc 1 M).card : ℝ) *
        (((1 / (2 * Real.pi) : ℝ) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖) +
          ((1 / (2 * Real.pi) : ℝ) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖)) := by
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
        ∑ m ∈ Finset.Icc 1 M,
          ‖gmTraceFourier cutoff t ((N : ℝ) * m) +
            gmTraceFourier cutoff t (-((N : ℝ) * m))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M,
        (((1 / (2 * Real.pi) : ℝ) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖) +
          ((1 / (2 * Real.pi) : ℝ) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hm
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact norm_gmTraceFourier_pos_le_mellinReflection
          cutoff t hN hmRange.1 hmRange.2
      · rw [gmTraceFourier_neg_eq_conj, norm_star]
        exact norm_gmTraceFourier_pos_le_mellinReflection
          cutoff (-t) hN hmRange.1 hmRange.2
    _ = ((Finset.Icc 1 M).card : ℝ) *
        (((1 / (2 * Real.pi) : ℝ) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖) +
          ((1 / (2 * Real.pi) : ℝ) *
            ∫ r : ℝ, ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖)) := by
      simp
      ring

end RiemannZeta.GuthMaynard
