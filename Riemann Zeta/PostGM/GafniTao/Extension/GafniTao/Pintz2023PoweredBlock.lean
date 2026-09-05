import GafniTao.Pintz2023Localization
import RiemannZeta.GuthMaynard.ClassicalPowering

/-!
# Pintz (2023), equations (4.15)--(4.16): the exact powered block

The first dyadic selection in `Pintz2023Localization` returns the literal
zero-padded source coefficient.  This module powers that exact coefficient
with the frozen finite-power construction and exposes its full
`(U^h,(2U)^h]` support as a wide Dirichlet polynomial.  A second exact
dyadic pigeonhole then produces the ordinary dyadic block required by the
frozen Montgomery--Halasz--Huxley theorem.

The construction deliberately powers the selected coefficient itself.  It
therefore retains a truncated final block and does not substitute Pintz's
full-block convolution for a different coefficient sequence.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The literal powered coefficient of the zero-padded block selected from
Pintz's source interval. -/
noncomputable def pintz2023SelectedPowerCoeff
    (X Y U h : ℕ) (beta : ℝ) (m : ℕ) : ℂ :=
  finitePowCoeff U h (pintz2023LocalizedLineCoeff X Y beta) m

/-- The same coefficient in the fixed-line normalization expected by the
wide-polynomial API.  The line parameter is zero because the real part
`beta` is already present in `pintz2023LocalizedLineCoeff`. -/
noncomputable def pintz2023SelectedPoweredLineCoeff
    (X Y U h : ℕ) (beta : ℝ) (m : ℕ) : ℂ :=
  finitePoweredLineCoeffs U h
    (pintz2023LocalizedLineCoeff X Y beta) 0 m

theorem pintz2023SelectedPoweredLineCoeff_eq
    (X Y U h : ℕ) (beta : ℝ) :
    pintz2023SelectedPoweredLineCoeff X Y U h beta =
      pintz2023SelectedPowerCoeff X Y U h beta := by
  funext m
  unfold pintz2023SelectedPoweredLineCoeff pintz2023SelectedPowerCoeff
    finitePoweredLineCoeffs
  simp

/-- The frozen finite-power object at imaginary argument is exactly the
power of the selected Dirichlet polynomial. -/
theorem pintz2023_finitePowPoly_eq_selected_block_power
    (X Y U h : ℕ) (beta t : ℝ) :
    finitePowPoly U h (pintz2023LocalizedLineCoeff X Y beta)
        ((t : ℂ) * I) =
      (dirichletPoly U (pintz2023LocalizedLineCoeff X Y beta) t) ^ h := by
  simp only [finitePowPoly, dirichletPoly, dyadicInterval, neg_mul]

/-- Exact wide-polynomial form of the powered selected block. -/
theorem wideDirichletPoly_pintz2023SelectedPoweredLineCoeff
    (X Y U h : ℕ) (beta t : ℝ) (hU : 0 < U) (hh : 0 < h) :
    wideDirichletPoly (U ^ h) h
        (pintz2023SelectedPoweredLineCoeff X Y U h beta) t =
      (dirichletPoly U (pintz2023LocalizedLineCoeff X Y beta) t) ^ h := by
  unfold pintz2023SelectedPoweredLineCoeff
  rw [wideDirichletPoly_finitePoweredLineCoeffs U h
    (pintz2023LocalizedLineCoeff X Y beta) 0 t hU hh]
  rw [show I * (t : ℂ) = (t : ℂ) * I by ring]
  simpa using
    pintz2023_finitePowPoly_eq_selected_block_power X Y U h beta t

/-- Raising a common selected-block lower bound gives the corresponding
lower bound for the exact wide powered polynomial. -/
theorem pintz2023_selected_block_power_lower
    {X Y U h : ℕ} {beta V : ℝ} {W : Finset ℝ}
    (hU : 0 < U) (hh : 0 < h) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly U
        (pintz2023LocalizedLineCoeff X Y beta) t‖) :
    ∀ t ∈ W, V ^ h ≤
      ‖wideDirichletPoly (U ^ h) h
        (pintz2023SelectedPoweredLineCoeff X Y U h beta) t‖ := by
  intro t ht
  rw [wideDirichletPoly_pintz2023SelectedPoweredLineCoeff
    X Y U h beta t hU hh, norm_pow]
  exact pow_le_pow_left₀ hV (hLarge t ht) h

/-- The second, post-powering dyadic extraction.  The output coefficients
remain the exact finite power of the source-selected coefficient. -/
theorem exists_pintz2023_powered_dyadic_block_and_subset
    {X Y U h : ℕ} {beta V : ℝ} {W : Finset ℝ}
    (hU : 0 < U) (hh : 0 < h) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly U
        (pintz2023LocalizedLineCoeff X Y beta) t‖) :
    ∃ r ∈ Finset.range h, ∃ W' ⊆ W,
      (W.card : ℝ) ≤ h * (W'.card : ℝ) ∧
      ∀ t ∈ W', V ^ h / h ≤
        ‖dirichletPoly (2 ^ r * U ^ h)
          (pintz2023SelectedPoweredLineCoeff X Y U h beta) t‖ := by
  have hwide := pintz2023_selected_block_power_lower hU hh hV hLarge
  exact exists_dyadic_block_and_subset (U ^ h) h
    (pintz2023SelectedPoweredLineCoeff X Y U h beta)
    W (V ^ h) hh hwide

#print axioms pintz2023SelectedPoweredLineCoeff_eq
#print axioms pintz2023_finitePowPoly_eq_selected_block_power
#print axioms wideDirichletPoly_pintz2023SelectedPoweredLineCoeff
#print axioms pintz2023_selected_block_power_lower
#print axioms exists_pintz2023_powered_dyadic_block_and_subset

end

end GafniTao
