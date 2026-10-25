import Dubon2026.SourceOriginalWeilComplexDatum
import Dubon2026.SourceOriginalComplexPicardMap
import Dubon2026.SourceOriginalWeilPairingDescent

/-! DUB-17/18 -> arithmetic Weil detection. The actual complex extension of
Weil representatives realizes the already constructed Picard comparison.
Its literal pairing identity therefore descends to the actual torsion pairing. -/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
local notation "FQ" => modularFunctionFieldOver N Qbar

theorem originalWeilComplexDatum_classLeft (d : OriginalWeilDatum N Qbar n) :
    (originalWeilComplexDatum N d).classLeft =
      ⟨complexPicardMap N d.classLeft.val,
        complexPicardMap_mem_torsion N d.classLeft.property⟩ := by
  exact Subtype.ext (complexPicardMap_mk N ⟨d.D₁, d.degree_first⟩).symm

theorem originalWeilComplexDatum_classRight (d : OriginalWeilDatum N Qbar n) :
    (originalWeilComplexDatum N d).classRight =
      ⟨complexPicardMap N d.classRight.val,
        complexPicardMap_mem_torsion N d.classRight.property⟩ := by
  exact Subtype.ext (complexPicardMap_mk N ⟨d.D₂, d.degree_second⟩).symm

theorem originalWeilPairing_complex
    (x y : Pic0.torsion (K := Qbar) (F := FQ) n) :
    ((originalWeilPairing N ℂ n
      ⟨complexPicardMap N x.val, complexPicardMap_mem_torsion N x.property⟩
      ⟨complexPicardMap N y.val, complexPicardMap_mem_torsion N y.property⟩ : ℂˣ) : ℂ) =
      sigma ((originalWeilPairing N Qbar n x y : Qbarˣ) : Qbar) := by
  obtain ⟨d, rfl, rfl⟩ := exists_original_weil_representative N Qbar n x y
  rw [← originalWeilComplexDatum_classLeft, ← originalWeilComplexDatum_classRight,
    originalWeilPairing_eq_pairing, originalWeilPairing_eq_pairing,
    originalWeilComplexDatum_pairing]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
