import GafniTao.HeathBrownLossyCells

/-!
# Heath--Brown low cells from the main cardinality estimate

When the unpowered source length is comparable with the physical height,
the main mean-value estimate already supplies both members of the ordinary
cardinality minimum.  This is the exact `p = 1` edge of the source argument;
it does not pretend that the usual `p >= 2` common-base transfer applies.
-/

namespace GafniTao

noncomputable section

/-- Lossy low-cell elimination using the main cardinality bound twice.  The
extra scale hypothesis is exactly what turns that bound into the constant
`3 - 3 sigma0` member of `heathBrownLowRhoCap`. -/
theorem heathBrown_lossy_low_cells_of_main
    {sigma0 sigmaMain tau rho rhoStar zetaRel zetaCard : Real}
    (hsigmaLower : 1 / 2 <= sigma0) (hsigmaUpper : sigma0 <= 3 / 4)
    (hSigmaMain : sigma0 <= sigmaMain)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (htauNear : tau <= 2 - sigma0)
    (hzetaRel : 0 <= zetaRel) (hzetaCard : 0 <= zetaCard)
    (hRhoMain : rho <= zetaCard + tau + 1 - 2 * sigmaMain)
    (hRelation : rhoStar <= zetaRel +
      (1 - 2 * sigmaMain +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    rhoStar <= max (heathBrownLowFirstSlope sigma0)
        (heathBrownLowSecondSlope sigma0) * tau +
      4 * (zetaRel + zetaCard) := by
  let rho0 := rho - zetaCard
  let rhoStar0 := rhoStar - 4 * (zetaRel + zetaCard)
  have hRhoFirst : rho0 <= tau + 1 - 2 * sigma0 := by
    dsimp only [rho0]
    linarith
  have hRhoSecond : rho0 <= 3 - 3 * sigma0 := by
    dsimp only [rho0]
    linarith
  have hExactMain := heathBrownExponentRelation_of_lossy_relation
    hzetaRel hzetaCard hRelation
  have hExact : HeathBrownExponentRelation sigma0 tau rho0 rhoStar0 :=
    hExactMain.mono_sigma hSigmaMain
  have hCell := heathBrown_low_scale_energy_slope hsigmaLower hsigmaUpper
    htauLower htauUpper (le_min hRhoFirst hRhoSecond) hExact
  dsimp only [rhoStar0] at hCell
  linarith

#print axioms heathBrown_lossy_low_cells_of_main

end

end GafniTao
