import GafniTao.HeathBrownLossyExponentRelation
import GafniTao.HeathBrownHighAlgebra

/-!
# Heath--Brown cell algebra with explicit finite losses

The source cell lemmas are exact.  This file applies them to the finite
packet after shifting the threshold, cardinality, and energy exponents.
All resulting errors are displayed as affine functions of the input losses.
-/

namespace GafniTao

noncomputable section

/-- The common loss in the two cardinality caps is `3*zetaCard/2`. -/
def heathBrownCardinalityShift (zetaCard : Real) : Real :=
  (3 / 2 : Real) * zetaCard

/-- Exact relation and cap after all finite packet losses are shifted out. -/
theorem heathBrown_lossy_packet_reduction
    {sigma0 sigmaMain sigmaNext tau rho rhoStar zetaRel zetaCard : Real}
    (hSigmaMain : sigma0 <= sigmaMain)
    (hSigmaNext : sigma0 <= sigmaNext)
    (hzetaRel : 0 <= zetaRel) (hzetaCard : 0 <= zetaCard)
    (hRhoMain : rho <= zetaCard + tau + 1 - 2 * sigmaMain)
    (hRhoNext : rho <= (3 / 2 : Real) *
      (zetaCard + 2 - 2 * sigmaNext))
    (hRelation : rhoStar <= zetaRel +
      (1 - 2 * sigmaMain +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    let L := heathBrownCardinalityShift zetaCard
    rho - L <= heathBrownLowRhoCap sigma0 tau /\
      HeathBrownExponentRelation sigma0 tau (rho - L)
        (rhoStar - 4 * (zetaRel + L)) := by
  dsimp only [heathBrownCardinalityShift]
  let L : Real := (3 / 2 : Real) * zetaCard
  have hL : 0 <= L := by dsimp only [L]; positivity
  have hMain : rho - L <= tau + 1 - 2 * sigma0 := by
    dsimp only [L]
    linarith
  have hNext : rho - L <= 3 - 3 * sigma0 := by
    dsimp only [L]
    linarith
  have hExactMain := heathBrownExponentRelation_of_lossy_relation
    hzetaRel hL hRelation
  have hExact := hExactMain.mono_sigma hSigmaMain
  exact ⟨le_min hMain hNext, hExact⟩

/-- First low-sigma cell, with every finite loss shown. -/
theorem heathBrown_lossy_first_cell
    {sigma0 sigmaMain sigmaNext tau rho rhoStar zetaRel zetaCard : Real}
    (hsigmaLower : 1 / 2 <= sigma0) (hsigmaUpper : sigma0 <= 2 / 3)
    (hSigmaMain : sigma0 <= sigmaMain)
    (hSigmaNext : sigma0 <= sigmaNext)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (hzetaRel : 0 <= zetaRel) (hzetaCard : 0 <= zetaCard)
    (hRhoMain : rho <= zetaCard + tau + 1 - 2 * sigmaMain)
    (hRhoNext : rho <= (3 / 2 : Real) *
      (zetaCard + 2 - 2 * sigmaNext))
    (hRelation : rhoStar <= zetaRel +
      (1 - 2 * sigmaMain +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    rhoStar <= heathBrownLowFirstSlope sigma0 * tau +
      4 * (zetaRel + heathBrownCardinalityShift zetaCard) := by
  have hReduced := heathBrown_lossy_packet_reduction hSigmaMain hSigmaNext
    hzetaRel hzetaCard hRhoMain hRhoNext hRelation
  dsimp only at hReduced
  have hCell := heathBrown_low_scale_first_cell hsigmaLower hsigmaUpper
    htauLower htauUpper hReduced.1 hReduced.2
  dsimp only [heathBrownCardinalityShift] at hCell ⊢
  linarith

/-- Second low-sigma cell, with every finite loss shown. -/
theorem heathBrown_lossy_second_cell
    {sigma0 sigmaMain sigmaNext tau rho rhoStar zetaRel zetaCard : Real}
    (hsigmaLower : 2 / 3 <= sigma0) (hsigmaUpper : sigma0 <= 3 / 4)
    (hSigmaMain : sigma0 <= sigmaMain)
    (hSigmaNext : sigma0 <= sigmaNext)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (hzetaRel : 0 <= zetaRel) (hzetaCard : 0 <= zetaCard)
    (hRhoMain : rho <= zetaCard + tau + 1 - 2 * sigmaMain)
    (hRhoNext : rho <= (3 / 2 : Real) *
      (zetaCard + 2 - 2 * sigmaNext))
    (hRelation : rhoStar <= zetaRel +
      (1 - 2 * sigmaMain +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    rhoStar <= heathBrownLowSecondSlope sigma0 * tau +
      4 * (zetaRel + heathBrownCardinalityShift zetaCard) := by
  have hReduced := heathBrown_lossy_packet_reduction hSigmaMain hSigmaNext
    hzetaRel hzetaCard hRhoMain hRhoNext hRelation
  dsimp only at hReduced
  have hCell := heathBrown_low_scale_second_cell hsigmaLower hsigmaUpper
    htauLower htauUpper hReduced.1 hReduced.2
  dsimp only [heathBrownCardinalityShift] at hCell ⊢
  linarith

/-- Unified form of the two low cells.  The maximum is later reduced to the
appropriate rational source slope at the exact transition `sigma0 = 2/3`. -/
theorem heathBrown_lossy_low_cells
    {sigma0 sigmaMain sigmaNext tau rho rhoStar zetaRel zetaCard : Real}
    (hsigmaLower : 1 / 2 <= sigma0) (hsigmaUpper : sigma0 <= 3 / 4)
    (hSigmaMain : sigma0 <= sigmaMain)
    (hSigmaNext : sigma0 <= sigmaNext)
    (htauLower : 1 <= tau) (htauUpper : tau <= 3 / 2)
    (hzetaRel : 0 <= zetaRel) (hzetaCard : 0 <= zetaCard)
    (hRhoMain : rho <= zetaCard + tau + 1 - 2 * sigmaMain)
    (hRhoNext : rho <= (3 / 2 : Real) *
      (zetaCard + 2 - 2 * sigmaNext))
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
      4 * (zetaRel + heathBrownCardinalityShift zetaCard) := by
  have htau : 0 <= tau := by linarith
  by_cases hsplit : sigma0 <= 2 / 3
  · have hFirst := heathBrown_lossy_first_cell hsigmaLower hsplit
      hSigmaMain hSigmaNext htauLower htauUpper hzetaRel hzetaCard
      hRhoMain hRhoNext hRelation
    calc
      rhoStar <= heathBrownLowFirstSlope sigma0 * tau +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) := hFirst
      _ <= max (heathBrownLowFirstSlope sigma0)
            (heathBrownLowSecondSlope sigma0) * tau +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) := by
        gcongr
        exact le_max_left _ _
  · have hSecond := heathBrown_lossy_second_cell (by linarith) hsigmaUpper
      hSigmaMain hSigmaNext htauLower htauUpper hzetaRel hzetaCard
      hRhoMain hRhoNext hRelation
    calc
      rhoStar <= heathBrownLowSecondSlope sigma0 * tau +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) := hSecond
      _ <= max (heathBrownLowFirstSlope sigma0)
            (heathBrownLowSecondSlope sigma0) * tau +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) := by
        gcongr
        exact le_max_right _ _

#print axioms heathBrown_lossy_packet_reduction
#print axioms heathBrown_lossy_first_cell
#print axioms heathBrown_lossy_second_cell
#print axioms heathBrown_lossy_low_cells

end

end GafniTao
