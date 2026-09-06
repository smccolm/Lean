import GafniTao.SourceSmoothDyadicEnergySplit
import GafniTao.LongTailSourceEnergySplit

/-!
# Exact reassembly of source-energy colourings

The two source decompositions colour the four coordinates of an additive
quadruple independently.  These lemmas cancel the literal factor four in
their mixed-to-self inequalities once a common bound is known for all four
selected families.  No asymptotic loss is discarded.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem SourceSmoothDyadicEnergyOutput.energy_le_of_all_cells
    {Y A r : Nat} {sigma V : Real} {W : Finset Real}
    (out : SourceSmoothDyadicEnergyOutput Y A r sigma V W)
    {M : Real}
    (hCell : forall i : Fin 4,
      (ApproxAddEnergy 1 (out.Ws i) : Real) <= M) :
    (ApproxAddEnergy 1 W : Real) <=
      (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card * M := by
  let F : Real :=
    (((Nat.clog 2 (A + 1)) ^ 4 : Nat) : Real) *
      (doubleFloorDefectWindow 1).card
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hSum :
      (ApproxAddEnergy 1 (out.Ws 0) : Real) +
          (ApproxAddEnergy 1 (out.Ws 1) : Real) +
          (ApproxAddEnergy 1 (out.Ws 2) : Real) +
          (ApproxAddEnergy 1 (out.Ws 3) : Real) <= 4 * M := by
    nlinarith [hCell 0, hCell 1, hCell 2, hCell 3]
  have hScaled := mul_le_mul_of_nonneg_left hSum hF
  have hRaw := out.hEnergy
  change 4 * (ApproxAddEnergy 1 W : Real) <= F *
    ((ApproxAddEnergy 1 (out.Ws 0) : Real) +
      (ApproxAddEnergy 1 (out.Ws 1) : Real) +
      (ApproxAddEnergy 1 (out.Ws 2) : Real) +
      (ApproxAddEnergy 1 (out.Ws 3) : Real)) at hRaw
  change (ApproxAddEnergy 1 W : Real) <= F * M
  nlinarith

theorem LongTailSourceEnergyOutput.energy_le_of_all_sources
    {Y A k : Nat} {sigma V : Real} {W : Finset Real}
    (out : LongTailSourceEnergyOutput Y A k sigma V W)
    {M : Real}
    (hSource : forall i : Fin 4,
      (ApproxAddEnergy 1 (out.Ws i) : Real) <= M) :
    (ApproxAddEnergy 1 W : Real) <=
      ((((k + 1) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card) * M := by
  let F : Real :=
    (((k + 1) ^ 4 : Nat) : Real) *
      (doubleFloorDefectWindow 1).card
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hSum :
      (ApproxAddEnergy 1 (out.Ws 0) : Real) +
          (ApproxAddEnergy 1 (out.Ws 1) : Real) +
          (ApproxAddEnergy 1 (out.Ws 2) : Real) +
          (ApproxAddEnergy 1 (out.Ws 3) : Real) <= 4 * M := by
    nlinarith [hSource 0, hSource 1, hSource 2, hSource 3]
  have hScaled := mul_le_mul_of_nonneg_left hSum hF
  have hRaw := out.hEnergy
  change 4 * (ApproxAddEnergy 1 W : Real) <= F *
    ((ApproxAddEnergy 1 (out.Ws 0) : Real) +
      (ApproxAddEnergy 1 (out.Ws 1) : Real) +
      (ApproxAddEnergy 1 (out.Ws 2) : Real) +
      (ApproxAddEnergy 1 (out.Ws 3) : Real)) at hRaw
  change (ApproxAddEnergy 1 W : Real) <= F * M
  nlinarith

#print axioms SourceSmoothDyadicEnergyOutput.energy_le_of_all_cells
#print axioms LongTailSourceEnergyOutput.energy_le_of_all_sources

end

end GafniTao
