import GafniTao.HeathBrownLossyExponentRelation
import GafniTao.HeathBrownHighAlgebra

/-!
# High Heath--Brown cell algebra with explicit finite losses

The exact high-cell lemma is stated for limiting exponents.  Finite packets
carry separate losses from Montgomery--Halasz--Huxley cardinality, the
next-power mean-value estimate, and the energy relation.  This file removes
all of them by one displayed affine shift before invoking the exact source
calculation.
-/

namespace GafniTao

noncomputable section

/-- The common cardinality shift needed by both high-cell caps. -/
def heathBrownHighCardinalityShift
    (tau zetaMHH epsilonMHH zetaNext : Real) : Real :=
  max (zetaMHH + epsilonMHH * tau)
    ((3 / 2 : Real) * zetaNext)

theorem heathBrownHighCardinalityShift_nonneg
    {tau zetaMHH epsilonMHH zetaNext : Real}
    (htau : 0 ≤ tau)
    (hzetaMHH : 0 ≤ zetaMHH) (hepsilonMHH : 0 ≤ epsilonMHH)
    (hzetaNext : 0 ≤ zetaNext) :
    0 ≤ heathBrownHighCardinalityShift tau zetaMHH epsilonMHH zetaNext := by
  unfold heathBrownHighCardinalityShift
  have hleft : 0 ≤ zetaMHH + epsilonMHH * tau := by
    positivity
  have hright : 0 ≤ (3 / 2 : Real) * zetaNext := by positivity
  calc
    0 = max (0 : Real) 0 := (max_self 0).symm
    _ ≤ max (zetaMHH + epsilonMHH * tau)
        ((3 / 2 : Real) * zetaNext) := max_le_max hleft hright

/-- Exact reduction of a lossy high packet to the source's two cardinality
caps and its self-referential energy relation. -/
theorem heathBrown_lossy_high_packet_reduction
    {sigma0 sigmaMain sigmaNext tau rho rhoStar
      zetaRel zetaMHH epsilonMHH zetaNext : Real}
    (hSigmaMain : sigma0 ≤ sigmaMain)
    (hSigmaNext : sigma0 ≤ sigmaNext)
    (hzetaRel : 0 ≤ zetaRel) (hzetaMHH : 0 ≤ zetaMHH)
    (hepsilonMHH : 0 ≤ epsilonMHH) (hzetaNext : 0 ≤ zetaNext)
    (htauNonneg : 0 ≤ tau)
    (hRhoMain : rho ≤ zetaMHH + epsilonMHH * tau +
      max (2 - 2 * sigmaMain) (tau + 4 - 6 * sigmaMain))
    (hRhoNext : rho ≤ (3 / 2 : Real) *
      (zetaNext + 2 - 2 * sigmaNext))
    (hRelation : rhoStar ≤ zetaRel +
      (1 - 2 * sigmaMain +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    let L := heathBrownHighCardinalityShift
      tau zetaMHH epsilonMHH zetaNext
    rho - L ≤ max (2 - 2 * sigma0) (tau + 4 - 6 * sigma0) ∧
      rho - L ≤ 3 - 3 * sigma0 ∧
      HeathBrownExponentRelation sigma0 tau (rho - L)
        (rhoStar - 4 * (zetaRel + L)) := by
  dsimp only
  let L := heathBrownHighCardinalityShift
    tau zetaMHH epsilonMHH zetaNext
  have hL : 0 ≤ L := heathBrownHighCardinalityShift_nonneg
    htauNonneg hzetaMHH hepsilonMHH hzetaNext
  have hMHHShift : zetaMHH + epsilonMHH * tau ≤ L := by
    exact le_max_left _ _
  have hNextShift : (3 / 2 : Real) * zetaNext ≤ L := by
    exact le_max_right _ _
  have hFirstMono : 2 - 2 * sigmaMain ≤ 2 - 2 * sigma0 := by
    linarith
  have hSecondMono : tau + 4 - 6 * sigmaMain ≤
      tau + 4 - 6 * sigma0 := by
    linarith
  have hMaxMono : max (2 - 2 * sigmaMain)
      (tau + 4 - 6 * sigmaMain) ≤
      max (2 - 2 * sigma0) (tau + 4 - 6 * sigma0) :=
    max_le (hFirstMono.trans (le_max_left _ _))
      (hSecondMono.trans (le_max_right _ _))
  have hMain : rho - L ≤
      max (2 - 2 * sigma0) (tau + 4 - 6 * sigma0) := by
    linarith
  have hNext : rho - L ≤ 3 - 3 * sigma0 := by
    linarith
  have hExactMain := heathBrownExponentRelation_of_lossy_relation
    hzetaRel hL hRelation
  have hExact := hExactMain.mono_sigma hSigmaMain
  exact ⟨hMain, hNext, hExact⟩

/-- The complete lossy high generic cell.  The output records exactly the
fourfold affine cost of removing the finite relation and cardinality losses.
-/
theorem heathBrown_lossy_high_generic_cell
    {sigma0 sigmaMain sigmaNext tau rho rhoStar
      zetaRel zetaMHH epsilonMHH zetaNext : Real}
    (hsigmaLower : 3 / 4 ≤ sigma0) (hsigmaUpper : sigma0 < 25 / 28)
    (hSigmaMain : sigma0 ≤ sigmaMain)
    (hSigmaNext : sigma0 ≤ sigmaNext)
    (htauLower : (4 * sigma0 - 1) / 2 ≤ tau)
    (htauUpper : tau ≤ 3 * (4 * sigma0 - 1) / 4)
    (hzetaRel : 0 ≤ zetaRel) (hzetaMHH : 0 ≤ zetaMHH)
    (hepsilonMHH : 0 ≤ epsilonMHH) (hzetaNext : 0 ≤ zetaNext)
    (hRhoMain : rho ≤ zetaMHH + epsilonMHH * tau +
      max (2 - 2 * sigmaMain) (tau + 4 - 6 * sigmaMain))
    (hRhoNext : rho ≤ (3 / 2 : Real) *
      (zetaNext + 2 - 2 * sigmaNext))
    (hRelation : rhoStar ≤ zetaRel +
      (1 - 2 * sigmaMain +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    rhoStar ≤ heathBrownHighEnergySlope sigma0 * tau +
      4 * (zetaRel + heathBrownHighCardinalityShift
        tau zetaMHH epsilonMHH zetaNext) := by
  have htauNonneg : 0 ≤ tau := by
    have hden : 0 < 4 * sigma0 - 1 := by linarith
    linarith
  have hReduced := heathBrown_lossy_high_packet_reduction
    hSigmaMain hSigmaNext hzetaRel hzetaMHH hepsilonMHH hzetaNext
    htauNonneg hRhoMain hRhoNext hRelation
  dsimp only at hReduced
  have hCell := heathBrown_high_generic_cell hsigmaLower hsigmaUpper
    htauLower htauUpper hReduced.1 hReduced.2.1 hReduced.2.2
  linarith

#print axioms heathBrown_lossy_high_packet_reduction
#print axioms heathBrown_lossy_high_generic_cell

end

end GafniTao
