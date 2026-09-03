import GafniTao.PintzEquation48

/-!
# Pintz's selected Dirichlet polynomial

This file removes the auxiliary contour coordinates from equation (4.9).
The resulting polynomial is exactly the finite Möbius polynomial at the
shifted physical ordinate; no coefficient or cutoff is changed.
-/

open Complex Set
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The physical finite polynomial on the right side of Pintz (4.9). -/
noncomputable def pintzDetectedPolynomial
    (xi lambda u : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (pintzMobiusCutoff lambda + 1),
    LSeries.term
      (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
      ((1 - xi : ℝ) + I * u) n

/-- The contour polynomial is literally the physical polynomial after the
equation-(4.7) change of variables. -/
theorem pintzFiniteMobiusPolynomial_leftLine_eq
    (Delta eta etaJ gamma lambda t : ℝ) :
    pintzFiniteMobiusPolynomial (pintzRho etaJ gamma) lambda
        ((pintzLeftEdge Delta eta etaJ : ℝ) + I * t) =
      pintzDetectedPolynomial (pintzXi Delta eta) lambda (gamma + t) := by
  unfold pintzFiniteMobiusPolynomial pintzDetectedPolynomial
  rw [pintz_rho_add_leftLine]
  simp

/-- Equation (4.9) in physical coordinates.  The selected ordinate remains
within the exact source window `[gamma-2*lambda,gamma+2*lambda]`. -/
theorem exists_large_pintzDetectedPolynomial
    {Delta eta etaJ gamma lambda F : ℝ}
    (hrhoZero : riemannZeta (pintzRho etaJ gamma) = 0)
    (hDelta : 0 < Delta) (hdeltaJ : 0 <= pintzDeltaJ eta etaJ)
    (hlambda : 0 < lambda) (hF : 0 < F)
    (hlower : 1 / 4 <=
      ‖pintzEquation46Integral Delta eta etaJ gamma lambda‖)
    (hFpoint : ∀ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
        ‖pintzF Delta eta etaJ gamma lambda t‖ <= F) :
    ∃ u ∈ Set.Icc (gamma - 2 * lambda) (gamma + 2 * lambda),
      1 / (32 * lambda * F) <=
        ‖pintzDetectedPolynomial (pintzXi Delta eta) lambda u‖ := by
  obtain ⟨t, ht, hlarge⟩ := exists_large_pintzFiniteMobiusPolynomial
    hrhoZero hDelta hdeltaJ hlambda hF hlower hFpoint
  refine ⟨gamma + t, ?_, ?_⟩
  · constructor <;> linarith [ht.1, ht.2]
  · rw [← pintzFiniteMobiusPolynomial_leftLine_eq]
    exact hlarge

#print axioms pintzFiniteMobiusPolynomial_leftLine_eq
#print axioms exists_large_pintzDetectedPolynomial

end

end GafniTao
