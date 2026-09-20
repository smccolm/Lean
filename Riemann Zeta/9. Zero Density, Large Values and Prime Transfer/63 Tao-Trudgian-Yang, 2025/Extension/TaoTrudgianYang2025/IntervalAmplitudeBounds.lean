import TaoTrudgianYang2025.ZetaAtkinsonSaddle
import GuthMaynard.LargeValuesReflection

/-!
# Concrete C1 amplitude bounds on an interval

The bound records the actual supremum and integral of the norm of
the derivative. Product rules preserve those literal analytic quantities;
the source application below must construct every bound it consumes.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace TaoTrudgianYang2025

structure IntervalC1Bound (f : ℝ → ℂ) (a b M : ℝ) : Prop where
  nonneg : 0 ≤ M
  smooth : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x
  norm_le : ∀ x ∈ Icc a b, ‖f x‖ ≤ M
  variation_le : (∫ x in a..b, ‖deriv f x‖) ≤ M

theorem IntervalC1Bound.derivative_integrable {f : ℝ → ℂ} {a b M : ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) :
    IntervalIntegrable (deriv f) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  exact ((hf.smooth x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

theorem IntervalC1Bound.mono {f : ℝ → ℂ} {a b M N : ℝ}
    (hf : IntervalC1Bound f a b M) (hMN : M ≤ N) : IntervalC1Bound f a b N :=
  ⟨hf.nonneg.trans hMN, hf.smooth, fun x hx => (hf.norm_le x hx).trans hMN,
    hf.variation_le.trans hMN⟩

theorem intervalC1Bound_const (c : ℂ) (a b : ℝ) :
    IntervalC1Bound (fun _ : ℝ => c) a b ‖c‖ := by
  refine ⟨norm_nonneg _, fun _ _ => contDiffAt_const, fun _ _ => le_rfl, ?_⟩
  simp only [deriv_const, norm_zero, intervalIntegral.integral_zero, norm_nonneg]

theorem IntervalC1Bound.mul {f g : ℝ → ℂ} {a b M N : ℝ}
    (hf : IntervalC1Bound f a b M) (hg : IntervalC1Bound g a b N) (hab : a ≤ b) :
    IntervalC1Bound (fun x => f x * g x) a b (2 * M * N) := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x :=
    ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt.mul
      ((hg.smooth x hx).differentiableAt (by norm_num)).hasDerivAt |>.deriv
  have hs : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 (fun y => f y * g y) x :=
    fun x hx => (hf.smooth x hx).mul (hg.smooth x hx)
  have hdi : IntervalIntegrable (deriv (fun x => f x * g x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact ((hs x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨by positivity [hf.nonneg, hg.nonneg], hs, ?_, ?_⟩
  · intro x hx
    rw [norm_mul]
    have h := mul_le_mul (hf.norm_le x hx) (hg.norm_le x hx) (norm_nonneg _) hf.nonneg
    nlinarith [mul_nonneg hf.nonneg hg.nonneg]
  · calc
      _ ≤ ∫ x in a..b, ‖deriv f x‖ * N + M * ‖deriv g x‖ := by
        apply intervalIntegral.integral_mono_on hab hdi.norm
          (((hf.derivative_integrable hab).norm.mul_const N).add
            ((hg.derivative_integrable hab).norm.const_mul M))
        intro x hx
        rw [hd x hx]
        apply (norm_add_le _ _).trans
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hg.norm_le x hx) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hf.norm_le x hx) (norm_nonneg _))
      _ = (∫ x in a..b, ‖deriv f x‖) * N + M * (∫ x in a..b, ‖deriv g x‖) := by
        rw [intervalIntegral.integral_add ((hf.derivative_integrable hab).norm.mul_const N)
          ((hg.derivative_integrable hab).norm.const_mul M),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
      _ ≤ M * N + M * N := add_le_add
        (mul_le_mul_of_nonneg_right hf.variation_le hg.nonneg)
        (mul_le_mul_of_nonneg_left hg.variation_le hf.nonneg)
      _ = _ := by ring

theorem intervalC1Bound_ofReal_of_deriv_nonneg {f : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hbound : ∀ x ∈ Icc a b, 0 ≤ f x ∧ f x ≤ M)
    (hd : ∀ x ∈ Icc a b, 0 ≤ deriv f x) :
    IntervalC1Bound (fun x => (f x : ℂ)) a b M := by
  have hfd (x : ℝ) (hx : x ∈ Icc a b) :=
    ((hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hcast (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun y => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) := (hfd x hx).ofReal_comp.deriv
  have hfi : IntervalIntegrable (deriv f) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact ((hf x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨hM, fun x hx => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hf x hx), ?_, ?_⟩
  · intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1]
    exact (hbound x hx).2
  · have heq : (∫ x in a..b, ‖deriv (fun y => (f y : ℂ)) x‖) =
        ∫ x in a..b, deriv f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      change ‖deriv (fun y : ℝ => (f y : ℂ)) x‖ = deriv f x
      rw [hcast x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd x hx)]
    rw [heq]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact hfd x hx) hfi]
    linarith [(hbound a ⟨le_rfl, hab⟩).1, (hbound b ⟨hab, le_rfl⟩).2]

theorem intervalC1Bound_ofReal_of_deriv_nonpos {f : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hbound : ∀ x ∈ Icc a b, 0 ≤ f x ∧ f x ≤ M)
    (hd : ∀ x ∈ Icc a b, deriv f x ≤ 0) :
    IntervalC1Bound (fun x => (f x : ℂ)) a b M := by
  have hfd (x : ℝ) (hx : x ∈ Icc a b) :=
    ((hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hcast (x : ℝ) (hx : x ∈ Icc a b) :
      deriv (fun y => (f y : ℂ)) x = ((deriv f x : ℝ) : ℂ) := (hfd x hx).ofReal_comp.deriv
  have hfi : IntervalIntegrable (deriv f) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact ((hf x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨hM, fun x hx => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hf x hx), ?_, ?_⟩
  · intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x hx).1]
    exact (hbound x hx).2
  · have heq : (∫ x in a..b, ‖deriv (fun y => (f y : ℂ)) x‖) =
        ∫ x in a..b, -deriv f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      change ‖deriv (fun y : ℝ => (f y : ℂ)) x‖ = -deriv f x
      rw [hcast x hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hd x hx)]
    rw [heq]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
        rw [uIcc_of_le hab] at hx
        exact hfd x hx) hfi]
    linarith [(hbound b ⟨hab, le_rfl⟩).1, (hbound a ⟨le_rfl, hab⟩).2]


theorem IntervalC1Bound.join {f : ℝ → ℂ} {a b c M N : ℝ}
    (hf : IntervalC1Bound f a b M) (hg : IntervalC1Bound f b c N)
    (hab : a ≤ b) (hbc : b ≤ c) : IntervalC1Bound f a c (M + N) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxb : x ≤ b
    · exact hf.smooth x ⟨hx.1, hxb⟩
    · exact hg.smooth x ⟨(lt_of_not_ge hxb).le, hx.2⟩
  · intro x hx
    by_cases hxb : x ≤ b
    · exact (hf.norm_le x ⟨hx.1, hxb⟩).trans (le_add_of_nonneg_right hg.nonneg)
    · exact (hg.norm_le x ⟨(lt_of_not_ge hxb).le, hx.2⟩).trans (le_add_of_nonneg_left hf.nonneg)
  · rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.derivative_integrable hab).norm (hg.derivative_integrable hbc).norm]
    exact add_le_add hf.variation_le hg.variation_le

theorem IntervalC1Bound.reflection {f : ℝ → ℂ} {T a b M : ℝ}
    (hf : IntervalC1Bound f a b M) (hT : 1 ≤ T) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, f x * ((x : ℂ)⁻¹ *
      Complex.exp (((T * Real.log x - 2 * Real.pi * x : ℝ) : ℂ) * I))‖ ≤
        20 * M / Real.sqrt T := by
  have h := RiemannZeta.GuthMaynard.norm_weighted_gmReflectionIntegral_le hT ha hab f (deriv f)
    (fun x hx => ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt)
    (hf.derivative_integrable hab)
  apply h.trans
  calc
    _ ≤ (10 / Real.sqrt T) * (M + M) := mul_le_mul_of_nonneg_left
      (add_le_add (hf.norm_le b ⟨hab, le_rfl⟩) hf.variation_le) (by positivity)
    _ = _ := by ring


theorem exists_intervalC1Bound_rescaled {f : ℝ → ℂ}
    (hf : ∀ x : ℝ, 0 < x → ContDiffAt ℝ 1 f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      IntervalC1Bound (fun x => f (x / T)) (T / 16) T C := by
  have hfc : ContinuousOn f (Icc (1 / 16 : ℝ) 1) :=
    fun x hx => (hf x (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv f) (Icc (1 / 16 : ℝ) 1) := fun x hx =>
    ((hf x (by linarith [hx.1])).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  let C : ℝ := 1 + |M| + |N|
  have hC : 0 < C := by dsimp [C]; positivity
  have hMC : M ≤ C := by dsimp [C]; linarith [le_abs_self M, abs_nonneg N]
  have hNC : N ≤ C := by dsimp [C]; linarith [le_abs_self N, abs_nonneg M]
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hscale (x : ℝ) (hx : x ∈ Icc (T / 16) T) : x / T ∈ Icc (1 / 16 : ℝ) 1 := by
    constructor
    · exact (le_div_iff₀ hT).mpr (by linarith [hx.1])
    · exact (div_le_one hT).mpr hx.2
  have hs (x : ℝ) (hx : x ∈ Icc (T / 16) T) : ContDiffAt ℝ 1 (fun y => f (y / T)) x :=
    (hf (x / T) (by linarith [(hscale x hx).1])).comp x (by fun_prop)
  have hd (x : ℝ) (hx : x ∈ Icc (T / 16) T) :
      deriv (fun y => f (y / T)) x = (1 / T : ℝ) • deriv f (x / T) := by
    exact (((hf (x / T) (by linarith [(hscale x hx).1])).differentiableAt
      (by norm_num)).hasDerivAt.scomp x ((hasDerivAt_id x).div_const T)).deriv
  have hdi : IntervalIntegrable (deriv (fun x => f (x / T))) volume (T / 16) T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : T / 16 ≤ T)]
    intro x hx
    exact ((hs x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  refine ⟨hC.le, hs, fun x hx => (hM (x / T) (hscale x hx)).trans hMC, ?_⟩
  calc
    _ ≤ ∫ x in (T / 16)..T, C / T := by
      apply intervalIntegral.integral_mono_on (by linarith) hdi.norm intervalIntegrable_const
      intro x hx
      rw [hd x hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / T)]
      have h := mul_le_mul_of_nonneg_left ((hN (x / T) (hscale x hx)).trans hNC)
        (by positivity : 0 ≤ 1 / T)
      convert h using 1
      ring
    _ = (T - T / 16) * (C / T) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ C := by
      have hfac : 0 ≤ C / T := by positivity
      calc
        _ ≤ T * (C / T) := mul_le_mul_of_nonneg_right (by linarith) hfac
        _ = C := by field_simp

end TaoTrudgianYang2025
