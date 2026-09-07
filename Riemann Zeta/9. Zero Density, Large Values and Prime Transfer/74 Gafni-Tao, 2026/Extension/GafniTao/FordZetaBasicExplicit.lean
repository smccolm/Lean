import GafniTao.FordZetaConvex

/-!
# Ford's explicit first-line zeta bounds

This file assembles the exact first line of Ford's `zeta basic` lemma from
the Euler-series inequalities and the centered-convexity estimate.
-/

open Complex

namespace GafniTao

theorem ford_norm_riemannZeta_real_le_explicit
    {sigma : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 53 / 50) :
    ‖riemannZeta (sigma : ℂ)‖ ≤ 3 / 5 + 1 / (sigma - 1) := by
  rw [ford_riemannZeta_real_norm hsigma]
  exact ford_riemannZeta_real_le_explicit hsigma hsigmaUpper

theorem ford_zeta_basic_upper
    {sigma t : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 53 / 50) :
    ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      3 / 5 + 1 / (sigma - 1) :=
  (ford_norm_riemannZeta_le_real hsigma).trans
    (ford_norm_riemannZeta_real_le_explicit hsigma hsigmaUpper)

theorem ford_zeta_basic_reciprocal_lower
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    1 / (riemannZeta (sigma : ℂ)).re ≤
      ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simp [s, hsigma]
  have hrealPos : 0 < (riemannZeta (sigma : ℂ)).re := by
    simpa using (riemannZeta_pos_of_one_lt hsigma).1
  have hnormPos : 0 < ‖riemannZeta s‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have hinv := ford_norm_riemannZeta_inv_le_real (sigma := sigma) (t := t) hsigma
  rw [norm_inv, ford_riemannZeta_real_norm hsigma] at hinv
  have hrecip := (inv_le_inv₀ hrealPos (inv_pos.mpr hnormPos)).mpr hinv
  simpa [s, one_div] using hrecip

theorem ford_zeta_basic_first_line
    {sigma t : ℝ} (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 53 / 50) :
    1 / (riemannZeta (sigma : ℂ)).re ≤
        ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ∧
      ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
        ‖riemannZeta (sigma : ℂ)‖ ∧
      ‖riemannZeta (sigma : ℂ)‖ ≤ 3 / 5 + 1 / (sigma - 1) := by
  exact ⟨ford_zeta_basic_reciprocal_lower hsigma,
    ford_norm_riemannZeta_le_real hsigma,
    ford_norm_riemannZeta_real_le_explicit hsigma hsigmaUpper⟩

end GafniTao
