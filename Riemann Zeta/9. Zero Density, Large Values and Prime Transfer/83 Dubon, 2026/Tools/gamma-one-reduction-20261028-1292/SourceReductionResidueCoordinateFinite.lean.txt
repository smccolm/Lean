import Dubon2026.SourceReductionFrame
import Mathlib.LinearAlgebra.Dimension.Finite

/-! DUB-17/18 -> original Gamma1 good reduction -> finite residue coordinate.
Reuse the native coordinate-field linear-independence lift for a regular
prolongation. Every finite independent residue family lifts to an independent
original family, bounding its size by the original degree. No equality of
degrees or genus is assumed; the Gamma1 consumer supplies the actual fields,
coordinate and original finite-degree theorem.
-/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_coordinate_rank_le (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F] :
    Module.rank (IntermediateField.adjoin (ResidueField A)
      ({R.residue x} : Set Fbar)) Fbar ≤
        Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F := by
  classical
  apply rank_le
  intro s hs
  let e := Fintype.equivFin s
  let v : Fin (Fintype.card s) → Fbar := fun i => (e.symm i).val
  have hv : LinearIndependent (IntermediateField.adjoin (ResidueField A)
      ({R.residue x} : Set Fbar)) v := hs.comp e.symm e.symm.injective
  choose y hy using fun i => R.residue_surjective (v i)
  have hyind : LinearIndependent (IntermediateField.adjoin (ResidueField A)
      ({R.residue x} : Set Fbar)) (fun i => R.residue (y i)) := by
    have he : (fun i => R.residue (y i)) = v := funext hy
    rw [he]
    exact hv
  have h := (linearIndependent_adjoinField R x hx y hyind).fintype_card_le_finrank
  simpa only [Fintype.card_fin, Fintype.card_coe] using h

theorem residue_coordinate_finite_and_finrank_le (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F] :
    FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({R.residue x} : Set Fbar)) Fbar ≤
          Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F := by
  have hr := residue_coordinate_rank_le R x hx
  refine ⟨?_, Module.finrank_le_of_rank_le hr⟩
  change Module.Finite (IntermediateField.adjoin (ResidueField A)
    ({R.residue x} : Set Fbar)) Fbar
  rw [← Module.rank_lt_aleph0_iff]
  exact lt_of_le_of_lt hr (Cardinal.natCast_lt_aleph0)

end
end Dubon2026.SourceCurve.RegularProlongation
