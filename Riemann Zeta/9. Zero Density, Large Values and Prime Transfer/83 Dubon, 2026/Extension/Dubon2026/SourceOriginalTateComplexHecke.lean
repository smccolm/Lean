import Dubon2026.SourceOriginalTateComparison
import Dubon2026.SourceOriginalHeckeComplexPicard

/-! DUB-17/18 -> original Tate Hecke realization -> arithmetic-to-complex
comparison. Apply existing Tate functoriality to the proved equivariance of
the actual original Picard map. The resulting actual Tate equivalence
intertwines the arithmetic and complex Hecke maps with no naturality premise.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem originalTateComplexEquiv_originalHecke (p : ℕ) [Fact p.Prime]
    (x : TateModule p (originalJZero N)) :
    originalTateComplexEquiv N p (TateModule.tateMap p (originalHeckePicard Qbar N ℓ) x) =
      TateModule.tateMap p (originalHeckePicard ℂ N ℓ) (originalTateComplexEquiv N p x) :=
  originalTateComplexEquiv_naturality N p (originalHeckePicard Qbar N ℓ)
    (originalHeckePicard ℂ N ℓ) (complexPicardMap_originalHeckePicard N ℓ) x

end
end Dubon2026.SourceFunctionField.OriginalConstantField
