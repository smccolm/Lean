import Dubon2026.SourceOriginalArithmeticWeilDetection
import Dubon2026.SourceOriginalTateWeilDetection

/-! DUB-17/18 -> primitive determinant -> required component pairing.
Actual finite Weil detection and the already proved finite-coordinate lifts
give nondegeneracy of the original arithmetic Tate pairing. Restricting it
nontrivially to the required Hecke component remains a separate obligation. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

theorem originalTateWeilPairing_detects
    (x : TateModule p (originalJZero N)) (hx : x ≠ 0) :
    ∃ y, originalTateWeilPairing N p x y ≠ 0 :=
  originalTateWeilPairing_detects_of_finiteLevel N p
    (fun k => originalArithmeticWeilPairing_detects N (p ^ k)) x hx

theorem originalTateWeilBilinear_injective :
    Function.Injective (originalTateWeilBilinear N p) :=
  originalTateWeilBilinear_injective_of_finiteLevel N p
    (fun k => originalArithmeticWeilPairing_detects N (p ^ k))

end
end Dubon2026.SourceFunctionField
