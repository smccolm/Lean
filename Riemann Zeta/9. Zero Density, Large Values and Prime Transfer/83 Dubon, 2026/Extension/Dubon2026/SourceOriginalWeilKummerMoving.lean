import Dubon2026.SourceOriginalWeilKummerDivisionNorm
import Dubon2026.SourceOriginalWeilKummerPointEvaluation
import Dubon2026.SourceCurveKummerRootPullback
import Dubon2026.SourceOriginalClosedPicardMoving

/-! DUB-17/18 -> finite Weil detection -> moved original representatives.
The proved original moving theorem avoids the finite restrictions of the
auxiliary norm data. The Picard quotient gives the principal correction;
the actual detecting consumer then applies the correction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
local notation "FF" => modularFunctionFieldOver N L

theorem originalWeil_move_divisor_with_correction (D : Divisor.degZero (K := L) (F := FF))
    (S : Finset (Place L FF)) :
    ∃ D' : Divisor.degZero (K := L) (F := FF), ∃ r : FF, r ≠ 0 ∧
      Pic0.mk D' = Pic0.mk D ∧
      (∀ v ∈ S, D'.val v = 0) ∧
      ∀ v, v.ord r = D'.val v - D.val v := by
  classical
  obtain ⟨D', hD', hav⟩ := originalPic0_representative_avoiding N L
    (Pic0.mk D) S
  have hq : Pic0.mk (D' - D) = 0 := by rw [map_sub, hD', sub_self]
  obtain ⟨r, hr, hord⟩ := (Pic0.mk_eq_zero_iff _).mp hq
  exact ⟨D', r, hr, hD', hav, fun v => (hord v).symm⟩

end
end Dubon2026.SourceFunctionField
