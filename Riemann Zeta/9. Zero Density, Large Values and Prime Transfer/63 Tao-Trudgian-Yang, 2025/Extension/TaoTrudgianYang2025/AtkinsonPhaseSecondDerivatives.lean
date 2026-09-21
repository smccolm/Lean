import TaoTrudgianYang2025.ZetaGaussianProfileSecondDerivatives

/-!
# Second derivatives of the actual non-frequency root phase

The phase is a fixed real profile multiplied by the physical height.
Its exponential is genuinely unit norm, and both chain-rule terms
are bounded uniformly at derivative scale T.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def atkinsonPhaseExponential (T v : ℝ) : ℂ := Complex.exp ((T * v : ℝ) * I)

theorem hasDerivAt_atkinsonPhaseExponential (T v : ℝ) :
    HasDerivAt (atkinsonPhaseExponential T)
      ((T : ℂ) * I * atkinsonPhaseExponential T v) v := by
  have h := ((((hasDerivAt_id v).const_mul T).ofReal_comp).mul_const I).cexp
  convert h using 1
  simp only [atkinsonPhaseExponential, Complex.ofReal_mul, mul_one, id_eq]
  ring

theorem iteratedDeriv_two_atkinsonPhaseExponential (T v : ℝ) :
    iteratedDeriv 2 (atkinsonPhaseExponential T) v =
      ((T : ℂ) * I) ^ 2 * atkinsonPhaseExponential T v := by
  have he : deriv (atkinsonPhaseExponential T) =
      fun w => (T : ℂ) * I * atkinsonPhaseExponential T w :=
    funext (fun w => (hasDerivAt_atkinsonPhaseExponential T w).deriv)
  have h := (hasDerivAt_atkinsonPhaseExponential T v).const_mul ((T : ℂ) * I)
  rw [iteratedDeriv_succ, iteratedDeriv_one, he]
  convert h.deriv using 1
  ring

theorem norm_atkinsonPhaseExponential_derivatives (T v : ℝ) :
    ‖atkinsonPhaseExponential T v‖ = 1 ∧
    ‖deriv (atkinsonPhaseExponential T) v‖ = |T| ∧
    ‖iteratedDeriv 2 (atkinsonPhaseExponential T) v‖ = T ^ 2 := by
  have hn : ‖atkinsonPhaseExponential T v‖ = 1 := by
    simp [atkinsonPhaseExponential, Complex.norm_exp, Complex.mul_re]
  refine ⟨hn, ?_, ?_⟩
  · rw [(hasDerivAt_atkinsonPhaseExponential T v).deriv]
    simp only [norm_mul, hn, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one]
  · rw [iteratedDeriv_two_atkinsonPhaseExponential]
    simp only [norm_mul, norm_pow, hn, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, sq_abs]

theorem exists_intervalC2Bound_phase_profile {v : ℝ → ℝ} {a b : ℝ}
    (hv : ∀ u ∈ Icc a b, ContDiffAt ℝ 2 v u) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      IntervalC2Bound (fun u => atkinsonPhaseExponential T (v u)) a b C T := by
  obtain ⟨M, hM, hprofile⟩ := exists_real_profile_derivative_bound hv
  let C : ℝ := 1 + M + M ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0 : 1 ≤ C := by dsimp [C]; nlinarith
  have hCM : M ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hE : ContDiff ℝ 2 (atkinsonPhaseExponential T) := by
    have hcast : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    unfold atkinsonPhaseExponential
    fun_prop
  refine ⟨hC.le, hT0.le, fun u hu => hE.contDiffAt.comp u (hv u hu), ?_, ?_, ?_⟩
  · intro u hu
    rw [(norm_atkinsonPhaseExponential_derivatives T (v u)).1]
    exact hC0
  · intro u hu
    have hd : HasDerivAt (fun w => atkinsonPhaseExponential T (v w))
        (deriv v u • deriv (atkinsonPhaseExponential T) (v u)) u :=
      (hE.differentiable (by norm_num)).differentiableAt.hasDerivAt.scomp
        (h := v) u ((hv u hu).differentiableAt (by norm_num)).hasDerivAt
    rw [hd.deriv, norm_smul, Real.norm_eq_abs,
      (norm_atkinsonPhaseExponential_derivatives T (v u)).2.1, abs_of_pos hT0]
    exact mul_le_mul_of_nonneg_right ((hprofile u hu).2.1.trans hCM) hT0.le
  · intro u hu
    rw [iteratedDeriv_two_comp_real hE.contDiffAt (hv u hu)]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs, abs_pow, sq_abs,
      (norm_atkinsonPhaseExponential_derivatives T (v u)).2.1,
      (norm_atkinsonPhaseExponential_derivatives T (v u)).2.2, abs_of_pos hT0]
    have hs := pow_le_pow_left₀ (abs_nonneg (deriv v u)) (hprofile u hu).2.1 2
    rw [sq_abs] at hs
    calc
      _ ≤ M ^ 2 * T ^ 2 + M * T :=
        add_le_add (mul_le_mul_of_nonneg_right hs (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (hprofile u hu).2.2 hT0.le)
      _ ≤ C * T ^ 2 := by
        have h := mul_le_mul_of_nonneg_left (show T ≤ T ^ 2 by nlinarith) hM.le
        dsimp [C]
        nlinarith

def atkinsonRootStationaryProfile (u : ℝ) : ℝ :=
  2 * Real.log u - 2 * Real.pi * u ^ 2

theorem exists_intervalC2Bound_atkinsonRootPhaseExponential :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      IntervalC2Bound (fun u => atkinsonPhaseExponential T (atkinsonRootStationaryProfile u))
        (1 / 4) 1 C T := by
  apply exists_intervalC2Bound_phase_profile
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  unfold atkinsonRootStationaryProfile
  fun_prop (disch := exact hu0.ne')

end TaoTrudgianYang2025
