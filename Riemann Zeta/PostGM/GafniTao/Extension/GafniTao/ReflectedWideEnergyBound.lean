import GafniTao.ReflectedWideEnergyOutput

/-!
# Reassembling all reflected energy cells

The reflection sign and dyadic label are four-coordinate colourings.  This
file bounds all sixteen retained self-energy cells before reassembling the
original family.  No maximum cell or cardinality-selected cell is used.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def reflectedDyadicExtractionFactor (H : Real) (k : Nat) : Real :=
  ((2 * k : Nat) : Real) ^ 4 *
    ((2 * ⌈H + 1⌉₊ + 1 : Nat) : Real) ^ 4 *
    (doubleFloorDefectWindow (1 + 4 * (H + 1))).card

/-- Exact reassembly from uniform estimates for all sixteen reflected
dyadic cells. -/
theorem ReflectedWideEnergyOutput.energy_le_of_all_cells
    {W : Finset Real} {H S R E : Real} {k : Nat} {a : Nat → Complex}
    (out : ReflectedWideEnergyOutput W H S R k a)
    (hCells : ∀ i j : Fin 4,
      (ApproxAddEnergy 1 (out.U i j) : Real) <= E) :
    (ApproxAddEnergy 1 W : Real) <=
      16 * (doubleFloorDefectWindow 1).card *
        reflectedDyadicExtractionFactor H k * E := by
  let F : Real := reflectedDyadicExtractionFactor H k
  have hF : 0 <= F := by
    dsimp only [F, reflectedDyadicExtractionFactor]
    positivity
  have hEachSign : ∀ i : Fin 4,
      (ApproxAddEnergy 1 (out.Ws i) : Real) <= F * E := by
    intro i
    have hSum :
        (ApproxAddEnergy 1 (out.U i 0) : Real) +
            (ApproxAddEnergy 1 (out.U i 1) : Real) +
            (ApproxAddEnergy 1 (out.U i 2) : Real) +
            (ApproxAddEnergy 1 (out.U i 3) : Real) <= 4 * E := by
      linarith [hCells i 0, hCells i 1, hCells i 2, hCells i 3]
    have hRaw := out.hDyadicEnergy i
    have hProduct :
        F * ((ApproxAddEnergy 1 (out.U i 0) : Real) +
            (ApproxAddEnergy 1 (out.U i 1) : Real) +
            (ApproxAddEnergy 1 (out.U i 2) : Real) +
            (ApproxAddEnergy 1 (out.U i 3) : Real)) <= F * (4 * E) :=
      mul_le_mul_of_nonneg_left hSum hF
    dsimp only [F, reflectedDyadicExtractionFactor] at hRaw hProduct ⊢
    nlinarith
  have hSignSum :
      (ApproxAddEnergy 1 (out.Ws 0) : Real) +
          (ApproxAddEnergy 1 (out.Ws 1) : Real) +
          (ApproxAddEnergy 1 (out.Ws 2) : Real) +
          (ApproxAddEnergy 1 (out.Ws 3) : Real) <= 4 * (F * E) := by
    linarith [hEachSign 0, hEachSign 1, hEachSign 2, hEachSign 3]
  have hOuterNonneg : (0 : Real) <=
      16 * ((doubleFloorDefectWindow 1).card : Real) := by positivity
  have hOuter := mul_le_mul_of_nonneg_left hSignSum hOuterNonneg
  have hRaw := out.hSignEnergy
  dsimp only [F] at hOuter ⊢
  nlinarith

#print axioms reflectedDyadicExtractionFactor
#print axioms ReflectedWideEnergyOutput.energy_le_of_all_cells

end

end GafniTao
