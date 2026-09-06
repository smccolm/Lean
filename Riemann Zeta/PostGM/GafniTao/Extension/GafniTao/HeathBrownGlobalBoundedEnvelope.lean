import GafniTao.DyadicZeroShellLoss

/-!
# The global bounded-shell alternative

This file closes the bounded member of the genuine global source
alternative.  It first casts the exact natural-valued shell cover to the
real majorant and then absorbs the literal fourth power of the number of
shells.  The detector alternative is deliberately not discarded.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- If the selected four-shell problem lands in its bounded member, the
genuine multiplicity-weighted four-zero count is bounded by the literal
global bounded-shell majorant, including the exact cover cardinality. -/
theorem zeroAdditiveEnergyCount_le_globalBoundedMajorant
    {sigma R0 T : Real} {coverLabel : Fin 4 -> Fin (dyadicZeroShellCount T)}
    (hCover : zeroAdditiveEnergyCount sigma T <=
      (dyadicZeroShellCount T) ^ 4 *
        weightedMixedAdditiveEnergyOn
          (dyadicZeroShell sigma T (coverLabel 0))
          (dyadicZeroShell sigma T (coverLabel 1))
          (dyadicZeroShell sigma T (coverLabel 2))
          (dyadicZeroShell sigma T (coverLabel 3))
          zeroMultiplicity 1)
    (hBounded :
      (weightedMixedAdditiveEnergyOn
          (dyadicZeroShell sigma T (coverLabel 0))
          (dyadicZeroShell sigma T (coverLabel 1))
          (dyadicZeroShell sigma T (coverLabel 2))
          (dyadicZeroShell sigma T (coverLabel 3))
          zeroMultiplicity 1 : Real) <=
        heathBrownBoundedShellMajorant sigma R0 T) :
    (zeroAdditiveEnergyCount sigma T : Real) <=
      (dyadicZeroShellCount T : Real) ^ 4 *
        heathBrownBoundedShellMajorant sigma R0 T := by
  have hCoverReal :
      (zeroAdditiveEnergyCount sigma T : Real) <=
        (dyadicZeroShellCount T : Real) ^ 4 *
          (weightedMixedAdditiveEnergyOn
            (dyadicZeroShell sigma T (coverLabel 0))
            (dyadicZeroShell sigma T (coverLabel 1))
            (dyadicZeroShell sigma T (coverLabel 2))
            (dyadicZeroShell sigma T (coverLabel 3))
            zeroMultiplicity 1 : Real) := by
    exact_mod_cast hCover
  exact hCoverReal.trans (mul_le_mul_of_nonneg_left hBounded (by positivity))

/-- The exact cover-factor times the bounded-shell majorant satisfies the
first Heath--Brown cell. -/
theorem heathBrownGlobalBoundedMajorant_first_cell
    {sigma R0 : Real} (hsigmaLower : 1 / 2 <= sigma)
    (hsigmaUpper : sigma <= 2 / 3) :
    EpsilonExponentBound
      (fun T => (dyadicZeroShellCount T : Real) ^ 4 *
        heathBrownBoundedShellMajorant sigma R0 T)
      (((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) *
        (1 - sigma)) :=
  (heathBrownBoundedShellMajorant_first_cell
    (R0 := R0) hsigmaLower hsigmaUpper).dyadic_shell_four_loss

/-- The exact cover-factor times the bounded-shell majorant satisfies the
second Heath--Brown cell. -/
theorem heathBrownGlobalBoundedMajorant_second_cell
    {sigma R0 : Real} (hsigmaLower : 2 / 3 <= sigma)
    (hsigmaUpper : sigma <= 3 / 4) :
    EpsilonExponentBound
      (fun T => (dyadicZeroShellCount T : Real) ^ 4 *
        heathBrownBoundedShellMajorant sigma R0 T)
      (((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) *
        (1 - sigma)) :=
  (heathBrownBoundedShellMajorant_second_cell
    (R0 := R0) hsigmaLower hsigmaUpper).dyadic_shell_four_loss

/-- The exact cover-factor times the bounded-shell majorant satisfies the
third Heath--Brown cell. -/
theorem heathBrownGlobalBoundedMajorant_third_cell
    {sigma R0 : Real} (hsigmaLower : 3 / 4 < sigma)
    (hsigmaUpper : sigma < 1) :
    EpsilonExponentBound
      (fun T => (dyadicZeroShellCount T : Real) ^ 4 *
        heathBrownBoundedShellMajorant sigma R0 T)
      ((12 / (4 * sigma - 1)) * (1 - sigma)) :=
  (heathBrownBoundedShellMajorant_third_cell
    (R0 := R0) hsigmaLower hsigmaUpper).dyadic_shell_four_loss

#print axioms zeroAdditiveEnergyCount_le_globalBoundedMajorant
#print axioms heathBrownGlobalBoundedMajorant_first_cell
#print axioms heathBrownGlobalBoundedMajorant_second_cell
#print axioms heathBrownGlobalBoundedMajorant_third_cell

end

end GafniTao
