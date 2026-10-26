import Dubon2026.SourceGammaOneCurveFinite
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> genuine Picard Hecke correspondence. The actual function fields
have proved finite coordinates, so the existing closed-residue theorem
discharges the residue-degree-one input for divisor norm and degree formulas. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem gamma1_place_residue_bijective (M : ℕ) [NeZero M]
    (v : Place L (laurentBaseChange L (x1FunctionField M))) :
    Function.Bijective (algebraMap L v.ResidueField) := by
  obtain ⟨t, _, ht⟩ := gamma1_finite_coordinate M L
  letI := ht
  exact place_residue_bijective_of_finite_coordinate t v

theorem gamma1_hecke_place_residue_bijective (M t : ℕ) [NeZero M] [NeZero t]
    (v : Place L (laurentBaseChange L (x1x0FunctionFieldC ℚ M t))) :
    Function.Bijective (algebraMap L v.ResidueField) := by
  obtain ⟨x, _, hx⟩ := gamma1_hecke_finite_coordinate M t L
  letI := hx
  exact place_residue_bijective_of_finite_coordinate x v

end
end Dubon2026.SourceFunctionField.GammaOne
