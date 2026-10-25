import Dubon2026.SourceOriginalWeilKummerDetection
import Dubon2026.SourceOriginalTateWeilDetection

/-! DUB-17/18 -> determinant -> original Tate nondegeneracy.
Combine the actual Kummer detecting-class argument with the already proved
finite-coordinate lifts. Finite-level detection is discharged in these
consumers; n-division of the displayed auxiliary point differences remains
explicit. No unconditional nondegeneracy or determinant is claimed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve OriginalChart Polynomial
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "FF" => modularFunctionFieldOver N Qbar

theorem originalTateWeilPairing_detects_of_kummer_point_division
    (hdivision : ∀ (k : ℕ) (a : FF), a ≠ 0 →
      ∀ (σ : Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X]) ≃ₐ[FF]
        Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X]))
        (w : Place Qbar (Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X]))),
        ∃ y : Pic0 Qbar (Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X])),
          (p ^ k) • y = Pic0.mk (K := Qbar) (F := Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X])) (originalWeilKummerPointDifference N Qbar (p ^ k) a σ w))
    (x : TateModule p (originalJZero N)) (hx : x ≠ 0) :
    ∃ y, originalTateWeilPairing N p x y ≠ 0 :=
  originalTateWeilPairing_detects_of_finiteLevel N p
    (fun k => originalWeilPairing_detects_of_kummer_point_division N Qbar (p ^ k) (hdivision k)) x hx

theorem originalTateWeilBilinear_injective_of_kummer_point_division
    (hdivision : ∀ (k : ℕ) (a : FF), a ≠ 0 →
      ∀ (σ : Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X]) ≃ₐ[FF]
        Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X]))
        (w : Place Qbar (Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X]))),
        ∃ y : Pic0 Qbar (Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X])),
          (p ^ k) • y = Pic0.mk (K := Qbar) (F := Polynomial.SplittingField (X ^ (p ^ k) - C a : FF[X])) (originalWeilKummerPointDifference N Qbar (p ^ k) a σ w)) :
    Function.Injective (originalTateWeilBilinear N p) :=
  originalTateWeilBilinear_injective_of_finiteLevel N p
    (fun k => originalWeilPairing_detects_of_kummer_point_division N Qbar (p ^ k) (hdivision k))

end
end Dubon2026.SourceFunctionField
