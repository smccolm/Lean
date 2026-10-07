import Dubon2026.RankinPerronContinuation
import Dubon2026.RankinRectanglePoles

/-! # The actual two residues of the Rankin Perron contour -/

namespace Dubon2026

open Complex CongruenceSubgroup Matrix.SpecialLinearGroup Set Filter
open scoped Topology

noncomputable section

/-- The actual holomorphic numerator remaining after the Perron poles at zero and one are separated. -/
def rankinPerronPoleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) (s : ℂ) : ℂ :=
  rankinConvolutionEntireNumerator f s * (x : ℂ) ^ (s + 2) / ((s + 1) * (s + 2))

/-- The actual separated Perron numerator is holomorphic on the full required contour domain. -/
theorem differentiableAt_rankinPerronPoleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (rankinPerronPoleNumerator f x) s := by
  have hs1 : s + 1 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith
  exact ((differentiable_rankinConvolutionEntireNumerator f s).mul
    ((differentiableAt_id.add_const (2 : ℂ)).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).div
    (by fun_prop) (mul_ne_zero hs1 hs2)

/-- The literal continued Perron integrand has exactly the two separated poles, with no change of function. -/
theorem rankinPerronContinuation_eq_pole_quotient {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) (s : ℂ) :
    rankinPerronContinuation f x s = rankinPerronPoleNumerator f x s / (s * (s - 1)) := by
  simp only [rankinPerronContinuation, rankinPerronPoleNumerator, rankinConvolutionGlobalContinuation,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual residue at one is the cubic Rankin main term. -/
theorem rankinPerronPoleNumerator_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (x : ℝ) :
    rankinPerronPoleNumerator f x 1 = (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 := by
  rw [rankinPerronPoleNumerator, rankinConvolutionEntireNumerator_one f hk]
  norm_num

/-- The zero-pole numerator is the exact quadratic contribution from the actual Rankin continuation. -/
theorem rankinPerronPoleNumerator_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : ℝ) :
    rankinPerronPoleNumerator f x 0 = rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 := by
  rw [rankinPerronPoleNumerator]
  norm_num

/-- The exact finite Rankin Perron rectangle encloses precisely the cubic main term and the genuine quadratic zero-pole term. -/
theorem rankinPerron_rectangle_residues {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {x T : ℝ} (hx : 0 < x) (hT : 0 < T) :
    RectangleIntegral' (rankinPerronContinuation f x) ((-1 / 8 : ℂ) - T * I) ((9 / 8 : ℂ) + T * I) =
      (rankinConvolutionResidue f : ℂ) * (x : ℂ) ^ 3 / 6 -
        rankinConvolutionEntireNumerator f 0 * (x : ℂ) ^ 2 / 2 := by
  have hre : ((-1 / 8 : ℂ) - T * I).re ≤ ((9 / 8 : ℂ) + T * I).re := by norm_num
  have him : ((-1 / 8 : ℂ) - T * I).im ≤ ((9 / 8 : ℂ) + T * I).im := by
    norm_num
    linarith
  have h0 : Rectangle ((-1 / 8 : ℂ) - T * I) ((9 / 8 : ℂ) + T * I) ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him]
    norm_num
    exact hT
  have h1 : Rectangle ((-1 / 8 : ℂ) - T * I) ((9 / 8 : ℂ) + T * I) ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him]
    norm_num
    exact hT
  have hH : DifferentiableOn ℂ (rankinPerronPoleNumerator f x)
      (Rectangle ((-1 / 8 : ℂ) - T * I) ((9 / 8 : ℂ) + T * I)) := by
    intro s hs
    have hslo : -1 / 8 ≤ s.re := by
      have hh := hs.1
      norm_num [Set.uIcc] at hh
      linarith [hh.1]
    exact (differentiableAt_rankinPerronPoleNumerator f hx (by linarith)).differentiableWithinAt
  have he := rectangle_two_pole_cauchy hre him h0 h1 hH
  rw [rankinPerronPoleNumerator_one f hk, rankinPerronPoleNumerator_zero] at he
  convert he using 1
  congr 1
  funext s
  exact rankinPerronContinuation_eq_pole_quotient f x s

end
end Dubon2026
