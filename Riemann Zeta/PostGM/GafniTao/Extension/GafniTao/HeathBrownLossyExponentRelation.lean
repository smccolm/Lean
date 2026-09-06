import GafniTao.HeathBrownActualExponentPacket
import GafniTao.HeathBrownExponentRelation

/-!
# Exact removal of finite losses from the exponent relation

The finite moment calculation produces equation (33) with a positive loss
and the mean-value bounds produce a positive loss in `rho`.  The affine
shift below removes both simultaneously.  The coefficient `4` is chosen so
that it dominates every occurrence of `rhoStar` and `rho` in the second
maximum; it is proved rather than hidden in `o(1)` notation.
-/

namespace GafniTao

noncomputable section

/-- Simultaneous loss removal for Heath--Brown's self-referential relation. -/
theorem heathBrownExponentRelation_of_lossy_relation
    {sigma tau rho rhoStar zeta L : Real}
    (hzeta : 0 <= zeta) (hL : 0 <= L)
    (hrel : rhoStar <= zeta +
      (1 - 2 * sigma +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2)))) :
    HeathBrownExponentRelation sigma tau (rho - L)
      (rhoStar - 4 * (zeta + L)) := by
  let rho0 := rho - L
  let rhoStar0 := rhoStar - 4 * (zeta + L)
  have hrho : rho = rho0 + L := by dsimp only [rho0]; ring
  have hrhoStar : rhoStar = rhoStar0 + 4 * (zeta + L) := by
    dsimp only [rhoStar0]
    ring
  have hFirst :
      max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) <=
        2 * L +
          max (rho0 + 1)
            (max (2 * rho0) (5 * rho0 / 4 + tau / 2)) := by
    rw [hrho]
    apply max_le
    · exact (show rho0 + L + 1 <= 2 * L +
          max (rho0 + 1)
            (max (2 * rho0) (5 * rho0 / 4 + tau / 2)) by
        linarith [le_max_left (rho0 + 1)
          (max (2 * rho0) (5 * rho0 / 4 + tau / 2))])
    apply max_le
    · exact (show 2 * (rho0 + L) <= 2 * L +
          max (rho0 + 1)
            (max (2 * rho0) (5 * rho0 / 4 + tau / 2)) by
        linarith [(le_max_left (2 * rho0)
          (5 * rho0 / 4 + tau / 2)).trans
            (le_max_right (rho0 + 1)
              (max (2 * rho0) (5 * rho0 / 4 + tau / 2)))])
    · exact (show 5 * (rho0 + L) / 4 + tau / 2 <= 2 * L +
          max (rho0 + 1)
            (max (2 * rho0) (5 * rho0 / 4 + tau / 2)) by
        linarith [(le_max_right (2 * rho0)
          (5 * rho0 / 4 + tau / 2)).trans
            (le_max_right (rho0 + 1)
              (max (2 * rho0) (5 * rho0 / 4 + tau / 2)))])
  have hShiftNonneg : 0 <= 4 * (zeta + L) := by positivity
  have hFourL : 4 * L <= 4 * (zeta + L) := by linarith
  have hThreeQuarter :
      3 * (4 * (zeta + L)) / 4 + L <= 4 * (zeta + L) := by
    linarith
  have hSecond :
      max (rhoStar + 1)
          (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2)) <=
        4 * (zeta + L) +
          max (rhoStar0 + 1)
            (max (4 * rho0)
              (3 * rhoStar0 / 4 + rho0 + tau / 2)) := by
    rw [hrho, hrhoStar]
    apply max_le
    · linarith [le_max_left (rhoStar0 + 1)
        (max (4 * rho0)
          (3 * rhoStar0 / 4 + rho0 + tau / 2))]
    apply max_le
    · linarith [(le_max_left (4 * rho0)
        (3 * rhoStar0 / 4 + rho0 + tau / 2)).trans
          (le_max_right (rhoStar0 + 1)
            (max (4 * rho0)
              (3 * rhoStar0 / 4 + rho0 + tau / 2)))]
    · linarith [(le_max_right (4 * rho0)
        (3 * rhoStar0 / 4 + rho0 + tau / 2)).trans
          (le_max_right (rhoStar0 + 1)
            (max (4 * rho0)
              (3 * rhoStar0 / 4 + rho0 + tau / 2)))]
  have hUpper :
      zeta +
          (1 - 2 * sigma +
            (1 / 2 : Real) *
              max (rho + 1)
                (max (2 * rho) (5 * rho / 4 + tau / 2)) +
            (1 / 2 : Real) *
              max (rhoStar + 1)
                (max (4 * rho)
                  (3 * rhoStar / 4 + rho + tau / 2))) <=
        4 * (zeta + L) +
          (1 - 2 * sigma +
            (1 / 2 : Real) *
              max (rho0 + 1)
                (max (2 * rho0) (5 * rho0 / 4 + tau / 2)) +
            (1 / 2 : Real) *
              max (rhoStar0 + 1)
                (max (4 * rho0)
                  (3 * rhoStar0 / 4 + rho0 + tau / 2))) := by
    linarith
  have hCombined := hrel.trans hUpper
  rw [hrhoStar] at hCombined
  have hResult : rhoStar0 <=
      1 - 2 * sigma +
        (1 / 2 : Real) *
          max (rho0 + 1)
            (max (2 * rho0) (5 * rho0 / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar0 + 1)
            (max (4 * rho0)
              (3 * rhoStar0 / 4 + rho0 + tau / 2)) := by
    linarith
  simpa only [rho0, rhoStar0, HeathBrownExponentRelation] using hResult

/-- A relation at a larger threshold exponent remains valid after lowering
that exponent. -/
theorem HeathBrownExponentRelation.mono_sigma
    {sigma sigma' tau rho rhoStar : Real}
    (hSigma : sigma <= sigma')
    (hrel : HeathBrownExponentRelation sigma' tau rho rhoStar) :
    HeathBrownExponentRelation sigma tau rho rhoStar := by
  unfold HeathBrownExponentRelation at hrel ⊢
  linarith

/-- A relation is monotone in the family-cardinality exponent. -/
theorem HeathBrownExponentRelation.mono_rho
    {sigma tau rho rho' rhoStar : Real}
    (hRho : rho <= rho')
    (hrel : HeathBrownExponentRelation sigma tau rho rhoStar) :
    HeathBrownExponentRelation sigma tau rho' rhoStar := by
  unfold HeathBrownExponentRelation at hrel ⊢
  have hFirst :
      max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) <=
        max (rho' + 1) (max (2 * rho') (5 * rho' / 4 + tau / 2)) := by
    gcongr
  have hSecond :
      max (rhoStar + 1)
          (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2)) <=
        max (rhoStar + 1)
          (max (4 * rho') (3 * rhoStar / 4 + rho' + tau / 2)) := by
    gcongr
  exact hrel.trans (by gcongr)

#print axioms heathBrownExponentRelation_of_lossy_relation
#print axioms HeathBrownExponentRelation.mono_sigma
#print axioms HeathBrownExponentRelation.mono_rho

end

end GafniTao
