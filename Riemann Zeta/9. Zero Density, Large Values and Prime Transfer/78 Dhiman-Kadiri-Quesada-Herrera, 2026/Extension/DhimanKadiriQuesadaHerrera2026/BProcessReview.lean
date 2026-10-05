import DhimanKadiriQuesadaHerrera2026.StationaryConstants

namespace DhimanKadiriQuesadaHerrera2026
namespace BProcessReview

/-- A genuine smooth phase whose lower derivative endpoint is close to the integer frequency one. -/
noncomputable def phase (u : ℝ) : ℝ := (651 / 200) * u - (151 / 200) * u ^ 2

/-- The review phase has derivatives of every finite order. -/
theorem phase_smooth : ContDiff ℝ 3 phase := by
  unfold phase
  fun_prop

/-- The phase realizes exactly the two derivative endpoints used by the diagnostic. -/
theorem phase_deriv (u : ℝ) : deriv phase u = 651 / 200 - 151 / 100 * u := by
  have h := (((hasDerivAt_id u).const_mul (651 / 200)).sub
    (((hasDerivAt_id u).pow 2).const_mul (151 / 200))).deriv
  convert h using 1
  simp only [id_eq]
  ring

/-- Constant negative curvature satisfies the source's second-derivative size condition. -/
theorem phase_second_deriv (u : ℝ) : deriv (deriv phase) u = -(151 / 100) := by
  have he : deriv phase = fun u => 651 / 200 - 151 / 100 * u := funext phase_deriv
  rw [he]
  convert ((hasDerivAt_const u (651 / 200)).sub ((hasDerivAt_id u).const_mul (151 / 100))).deriv using 1
  norm_num

/-- The third derivative vanishes identically, so the diagnostic does not rely on a rough phase. -/
theorem phase_third_deriv (u : ℝ) : deriv (deriv (deriv phase)) u = 0 := by
  have he : deriv (deriv phase) = fun _ => -(151 / 100 : ℝ) := funext phase_second_deriv
  rw [he]
  exact deriv_const u _

/-- The actual derivative interval is positive and strictly decreasing with its lower endpoint below one. -/
theorem phase_source_range :
    deriv phase (1 / 2) = 5 / 2 ∧ deriv phase (3 / 2) = 99 / 100 ∧
    StrictAntiOn (deriv phase) (Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧
    (∀ u ∈ Set.Icc (1 / 2 : ℝ) (3 / 2), 0 < deriv phase u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [phase_deriv]
  · norm_num [phase_deriv]
  · intro u _ v _ huv
    rw [phase_deriv, phase_deriv]
    linarith
  · intro u hu
    rw [phase_deriv]
    linarith [hu.2]

/-- The reciprocal endpoint majorant in the cited stationary-phase argument does not obey the claimed logarithmic cap on the paper's chosen interior range. -/
theorem interior_reciprocal_bound_fails :
    2 / Real.pi * Real.log ((5 / 2 : ℝ) - 99 / 100) + 1.251 <
      ∑ ν ∈ Finset.Icc 1 (⌊(5 / 2 : ℝ)⌋₊ - 1),
        (1 / Real.pi) * (1 / |(5 / 2 : ℝ) - ν| + 1 / |(ν : ℝ) - 99 / 100|) := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 151 / 100)
  have hp := Real.pi_lt_four
  have hr : (∑ ν ∈ Finset.Icc 1 (⌊(5 / 2 : ℝ)⌋₊ - 1),
        (1 / Real.pi) * (1 / |(5 / 2 : ℝ) - ν| + 1 / |(ν : ℝ) - 99 / 100|)) =
      (302 / 3) / Real.pi := by
    norm_num
    ring
  rw [hr]
  apply (lt_div_iff₀ Real.pi_pos).mpr
  have he : (2 / Real.pi * Real.log ((5 / 2 : ℝ) - 99 / 100) + 1.251) * Real.pi =
      2 * Real.log (151 / 100) + 1.251 * Real.pi := by
    norm_num
    field_simp
  rw [he]
  nlinarith

/-- Removing the last stationary frequency removes a nonzero term of its exact curvature scale. -/
theorem omitted_stationary_term_norm (f : ℝ → ℝ) (ξ : ℕ → ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ‖(∑ ν ∈ Finset.Icc 1 M,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - ν * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)) -
      ∑ ν ∈ Finset.Icc 1 (M - 1),
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - ν * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ = 1 / Real.sqrt |deriv (deriv f) (ξ M)| := by
  have he : M = (M - 1) + 1 := by omega
  conv_lhs => arg 1; lhs; rw [he, Finset.sum_Icc_succ_top (by omega)]
  rw [← he, add_sub_cancel_left, norm_div]
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

end BProcessReview
end DhimanKadiriQuesadaHerrera2026
