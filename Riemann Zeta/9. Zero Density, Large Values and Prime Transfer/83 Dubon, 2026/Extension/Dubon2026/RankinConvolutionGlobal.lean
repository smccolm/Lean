import Dubon2026.RankinConvolutionCompleted
import Dubon2026.RankinConvolutionRegular
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Global meromorphic continuation of the actual Rankin convolution series -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The exact reciprocal completion factor after absorbing the factor s by Gamma recurrence. -/
def rankinConvolutionInverseFactor (k : ℤ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ s * (4 * Real.pi : ℂ) ^ (s + (k : ℂ) - 1) *
    (Gamma (s + 1))⁻¹ * (Gamma (s + (k : ℂ) - 1))⁻¹

/-- Reciprocal Gamma makes the actual inverse completion factor entire, including all Gamma poles. -/
theorem differentiable_rankinConvolutionInverseFactor (k : ℤ) :
    Differentiable ℂ (rankinConvolutionInverseFactor k) := by
  intro s
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h4π : (4 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z + (k : ℂ) - 1) s := by fun_prop
  have hG1 : DifferentiableAt ℂ (fun z : ℂ => (Gamma (z + 1))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma (s + 1)).comp (g := fun z : ℂ => (Gamma z)⁻¹) (f := fun z : ℂ => z + 1) s
      (show DifferentiableAt ℂ (fun z : ℂ => z + 1) s by fun_prop)
  have hGk : DifferentiableAt ℂ (fun z : ℂ => (Gamma (z + (k : ℂ) - 1))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma (s + (k : ℂ) - 1)).comp (g := fun z : ℂ => (Gamma z)⁻¹) (f := fun z : ℂ => z + (k : ℂ) - 1) s hshift
  exact (((differentiableAt_id.const_cpow (Or.inl hπ)).mul
    (hshift.const_cpow (Or.inl h4π))).mul hG1).mul hGk

/-- The actual global pole numerator, obtained from the genuine entire lattice completion. -/
def rankinConvolutionEntireNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  gamma0CuspEntire f s * rankinConvolutionInverseFactor k s

/-- The genuine Rankin convolution pole numerator extends to an entire function. -/
theorem differentiable_rankinConvolutionEntireNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    Differentiable ℂ (rankinConvolutionEntireNumerator f) :=
  (differentiable_gamma0CuspEntire f).mul (differentiable_rankinConvolutionInverseFactor k)

/-- In the convergence half-plane the actual entire numerator is precisely (s-1) times the original series. -/
theorem rankinConvolutionEntireNumerator_eq_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    rankinConvolutionEntireNumerator f s = (s - 1) * LSeries (rankinConvolutionCoefficients f) s := by
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h4π : (4 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hGs : Gamma (s + (k : ℂ) - 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [sub_re, add_re, intCast_re, one_re]
    linarith)
  have hpπ : (Real.pi : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have hp4 : (4 * Real.pi : ℂ) ^ (s + (k : ℂ) - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h4π)
  rw [rankinConvolutionEntireNumerator, gamma0CuspEntire_eq_convolution f hk hs]
  simp only [rankinConvolutionInverseFactor, cuspRankinFactor, Gamma_add_one s hs0, Complex.cpow_neg]
  field_simp [hs0, hG, hGs, hpπ, hp4]

/-- The actual globally continued Rankin convolution, away from its pole at one. -/
def rankinConvolutionGlobalContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  rankinConvolutionEntireNumerator f s / (s - 1)

/-- The genuine global continuation is holomorphic everywhere except the possible pole at one. -/
theorem differentiableAt_rankinConvolutionGlobalContinuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (rankinConvolutionGlobalContinuation f) s :=
  (differentiable_rankinConvolutionEntireNumerator f s).div (by fun_prop) (sub_ne_zero.mpr hs)

/-- The actual globally continued function agrees with its original coefficient series on Re(s)>1. -/
theorem rankinConvolutionGlobalContinuation_eq_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    rankinConvolutionGlobalContinuation f s = LSeries (rankinConvolutionCoefficients f) s := by
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re] at hs; linarith
  rw [rankinConvolutionGlobalContinuation, rankinConvolutionEntireNumerator_eq_series f hk hs]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)

end
end Dubon2026
