import Dubon2026.SourceOriginalWeilKummerMoving
import Dubon2026.SourceCurveKummerNormAvoidance

/-! DUB-17/18 -> actual detecting datum -> disjoint norm representatives.
Native original moving avoids the two cover points and the norm-divisor
support. This derives all the vanishing conditions needed by the detecting
ratio from the actual principal norm data. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "FF" => modularFunctionFieldOver N L
local notation "EE" => Polynomial.SplittingField (X ^ n - C f)

theorem exists_originalWeilKummer_norm_avoiding
    (D : Divisor.degZero (K := L) (F := FF)) (σ : EE ≃ₐ[FF] EE) (w : Place L EE)
    (B : Divisor L EE) (u : EE)
    (hU : ∀ q : Place L EE, q.ord u =
      (originalWeilKummerPointDifference N L n f σ w).val q + n * B q) :
    let ι : Place L EE → Place L FF := fun q : Place L EE => q.restrict FF
    ∃ D' : Divisor.degZero (K := L) (F := FF), ∃ r : FF, r ≠ 0 ∧
      Pic0.mk D' = Pic0.mk D ∧
      (∀ v : Place L FF, v.ord r = D'.val v - D.val v) ∧
      (∀ v : Place L FF, D'.val v = 0 ∨ Divisor.geometricPushforward FF B v = 0) ∧
      (∀ q : Place L EE, q ∈ (originalWeilKummerPointDifference N L n f σ w).val.support →
        D'.val (ι q) = 0) ∧
      (∀ q : Place L EE, q ∈ B.support → D'.val (ι q) = 0) ∧
      D'.val (ι w) = 0 ∧
      (∀ v : Place L FF, v ∈ D'.val.support → ∀ q : Place L EE, ι q = v → q.ord u = 0) ∧
      ∀ q : Place L EE, q.ord u ≠ 0 → D'.val (ι q) = 0 := by
  exact exists_kummer_norm_avoiding n D w (w.comapEquiv (σ.restrictScalars L)) B u hU
    (originalWeil_move_divisor_with_correction N L D)

end
end Dubon2026.SourceFunctionField
