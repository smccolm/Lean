import GafniTao.Pintz2023Equation47TruncationBound
import GafniTao.Pintz2023Equation42Quantitative
import GafniTao.Pintz2023Localization
import GafniTao.HeathBrownHybridZetaSum

/-!
# Pintz (2023), equations (4.7)--(4.12): the physical detected polynomial

This file identifies the finite polynomial left by the completed contour
shift with the coefficient object localized later in equations (4.13)--(4.15).
No coefficient sequence is changed at this interface.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The exponent on the detected source polynomial after shifting from the
zero `1-etaJ+i gamma` to the line `Re s = 1/lambda`. -/
noncomputable def pintz2023DetectedBeta (etaJ lambda : ℝ) : ℝ :=
  1 - etaJ + 1 / lambda

/-- Exact physical-coordinate form of the finite polynomial in (4.7). -/
theorem pintz2023Equation47Polynomial_eq_truncated
    {X : ℕ} {etaJ gamma lambda t : ℝ} (hX : 0 < X) :
    pintz2023Equation47Polynomial X (pintz2023Rho etaJ gamma) lambda t =
      pintz2023TruncatedPolynomial X (pintz2023Cutoff lambda)
        (pintz2023DetectedBeta etaJ lambda) (gamma + t) := by
  rw [pintz2023_truncated_eq_complex_power _ _ hX]
  unfold pintz2023Equation47Polynomial pintz2023DetectedBeta
    pintz2023Equation47Shift pintz2023Rho
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := lt_trans hX (Finset.mem_Ioc.mp hn).1
  rw [LSeries.term_of_ne_zero (by omega)]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  congr 2
  push_cast
  ring

#print axioms pintz2023Equation47Polynomial_eq_truncated

end

end GafniTao
