import Dubon2026.BinomialJessen
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Int.Interval

/-! # Actual simple zeros of the two-term exponential polynomial -/

namespace Dubon2026

open Complex

noncomputable section

/-- The full zero lattice, with the positive sign convention used in the paper. -/
def binomialZero (κ : ℝ) (m : ℤ) : ℂ :=
  (((2 * (m : ℝ) + 1) * Real.pi / κ : ℝ) : ℂ) * Complex.I

theorem binomialZero_injective {κ : ℝ} (hκ : κ ≠ 0) :
    Function.Injective (binomialZero κ) := by
  intro m n h
  have hi := congrArg Complex.im h
  simp only [binomialZero, Complex.mul_I_im, Complex.ofReal_re] at hi
  have he := (div_left_inj' hκ).mp hi
  have he' := (mul_left_inj' Real.pi_ne_zero).mp he
  have hc : (m : ℝ) = n := by linarith
  exact_mod_cast hc

theorem binomialDirichlet_zero_iff {κ : ℝ} (hκ : κ ≠ 0) (s : ℂ) :
    binomialDirichlet κ s = 0 ↔ ∃ m : ℤ, s = binomialZero κ m := by
  have hk : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  constructor
  · intro hz
    have he : Complex.exp (-(κ : ℂ) * s) = Complex.exp (Real.pi * Complex.I) := by
      rw [Complex.exp_pi_mul_I]
      have hh := congrArg (fun z : ℂ => z - 1) hz
      simpa only [binomialDirichlet, add_sub_cancel_left, zero_sub] using hh
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    refine ⟨-n - 1, ?_⟩
    unfold binomialZero
    push_cast
    apply (mul_left_cancel₀ hk)
    field_simp
    linear_combination -hn
  · rintro ⟨m, rfl⟩
    have he : -(κ : ℂ) * binomialZero κ m =
        (Real.pi : ℂ) * Complex.I + ((-m - 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      unfold binomialZero
      push_cast
      field_simp
      ring
    have hh := Complex.exp_eq_exp_iff_exists_int.mpr ⟨-m - 1, he⟩
    rw [binomialDirichlet, hh, Complex.exp_pi_mul_I]
    ring

theorem hasDerivAt_binomialDirichlet (κ : ℝ) (s : ℂ) :
    HasDerivAt (binomialDirichlet κ)
      (Complex.exp (-(κ : ℂ) * s) * -(κ : ℂ)) s := by
  simpa only [mul_one, binomialDirichlet] using
    ((((hasDerivAt_id s).const_mul (-(κ : ℂ))).cexp).const_add 1)

theorem analyticAt_binomialDirichlet (κ : ℝ) (s : ℂ) :
    AnalyticAt ℂ (binomialDirichlet κ) s := by
  unfold binomialDirichlet
  fun_prop

theorem analyticOrderNatAt_binomial_zero {κ : ℝ} (hκ : κ ≠ 0) {s : ℂ}
    (hs : binomialDirichlet κ s = 0) : analyticOrderNatAt (binomialDirichlet κ) s = 1 := by
  have hd : deriv (binomialDirichlet κ) s ≠ 0 := by
    rw [(hasDerivAt_binomialDirichlet κ s).deriv]
    exact mul_ne_zero (Complex.exp_ne_zero _) (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hκ))
  have ho := (analyticAt_binomialDirichlet κ s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hs hd
  simp [analyticOrderNatAt, ho]

theorem binomialZero_re (κ : ℝ) (m : ℤ) : (binomialZero κ m).re = 0 := by
  simp [binomialZero]

theorem binomialZero_im (κ : ℝ) (m : ℤ) :
    (binomialZero κ m).im = (2 * (m : ℝ) + 1) * Real.pi / κ := by
  simp [binomialZero]

end

end Dubon2026
