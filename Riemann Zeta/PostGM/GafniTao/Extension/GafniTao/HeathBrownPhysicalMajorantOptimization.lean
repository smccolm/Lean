import GafniTao.HeathBrownPhysicalMajorantEnvelope
import GafniTao.HeathBrownLowSlopeContinuity

/-!
# Finite optimization of the physical low-cell majorants

This is the exact real-variable endpoint of the low-cell calculation.  The
three reserve inequalities are deliberately visible: direct Type I,
reflected Type I, and powered Type II.  A later parameter selector proves
all three from one requested epsilon budget.
-/

namespace GafniTao

noncomputable section

theorem heathBrown_physical_majorant_exponents_le
    {sigma sigma0 d zetaExtract zetaRel zetaCard zetaFixed eta zetaShell
        zetaConst zetaDil delta2 epsilon : Real}
    (hsigmaUpper : sigma <= 3 / 4)
    (hsigma0Lower : 1 / 2 <= sigma0) (hsigma0Order : sigma0 <= sigma)
    (hTypeIReserve :
      7 * (sigma - sigma0) +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) + zetaFixed <=
        epsilon)
    (hReflectedReserve :
      zetaExtract + 2 * d * heathBrownLowCellExponent sigma0 zetaRel zetaCard +
          7 * (sigma - sigma0) +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) + zetaFixed <=
        epsilon)
    (hTypeIILower : 1 / 2 <=
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst
        (Nat.ceil (4 / delta2) + 1) - zetaDil)
    (hTypeIIOrder :
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst
          (Nat.ceil (4 / delta2) + 1) - zetaDil <= sigma)
    (hTypeIIReserve :
      7 * (sigma -
          (heathBrownEffectiveSigma sigma eta zetaShell zetaConst
            (Nat.ceil (4 / delta2) + 1) - zetaDil)) +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard) + zetaFixed <=
        epsilon) :
    max
        (heathBrownTypeIEnvelopeExponent d zetaExtract sigma0 zetaRel
          zetaCard zetaFixed)
        (heathBrownTypeIIEnvelopeExponent sigma eta zetaShell zetaConst
          zetaDil zetaRel zetaCard delta2 zetaFixed) <=
      max (heathBrownLowFirstSlope sigma) (heathBrownLowSecondSlope sigma) +
        epsilon := by
  let L := max (heathBrownLowFirstSlope sigma)
    (heathBrownLowSecondSlope sigma)
  let L0 := max (heathBrownLowFirstSlope sigma0)
    (heathBrownLowSecondSlope sigma0)
  let sigmaII := heathBrownEffectiveSigma sigma eta zetaShell zetaConst
    (Nat.ceil (4 / delta2) + 1) - zetaDil
  let LII := max (heathBrownLowFirstSlope sigmaII)
    (heathBrownLowSecondSlope sigmaII)
  have hL0 : L0 <= L + 7 * (sigma - sigma0) := by
    exact heathBrownLowMaxSlope_lipschitz hsigma0Lower hsigmaUpper hsigma0Order
  have hLII : LII <= L + 7 * (sigma - sigmaII) := by
    exact heathBrownLowMaxSlope_lipschitz hTypeIILower hsigmaUpper hTypeIIOrder
  have hDirect :
      heathBrownLowCellExponent sigma0 zetaRel zetaCard + zetaFixed <=
        L + epsilon := by
    dsimp only [heathBrownLowCellExponent, L0, L] at hL0
    dsimp only [L, heathBrownCardinalityShift] at hTypeIReserve
    dsimp only [L, heathBrownLowCellExponent, heathBrownCardinalityShift]
    linarith
  have hReflected :
      zetaExtract + reflectedPhysicalBeta d *
          heathBrownLowCellExponent sigma0 zetaRel zetaCard + zetaFixed <=
        L + epsilon := by
    dsimp only [heathBrownLowCellExponent, L0, L] at hL0
    dsimp only [L, reflectedPhysicalBeta, heathBrownLowCellExponent,
      heathBrownCardinalityShift]
      at hReflectedReserve
    dsimp only [L, reflectedPhysicalBeta, heathBrownLowCellExponent,
      heathBrownCardinalityShift]
    nlinarith
  have hII :
      LII + 4 * (zetaRel + heathBrownCardinalityShift zetaCard) + zetaFixed <=
        L + epsilon := by
    dsimp only [L, sigmaII, LII, heathBrownCardinalityShift]
      at hLII hTypeIIReserve
    dsimp only [L, LII, heathBrownCardinalityShift]
    linarith
  rw [max_le_iff]
  constructor
  · dsimp only [heathBrownTypeIEnvelopeExponent]
    exact max_le hDirect hReflected
  · simpa only [heathBrownTypeIIEnvelopeExponent, sigmaII, LII] using hII

#print axioms heathBrown_physical_majorant_exponents_le

end

end GafniTao
