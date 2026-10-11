import Dubon2026.LocalCoefficientFiberProduct
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.Ring

/-! # Genuine coefficient maps for adding and scaling first-order deformations -/

namespace Dubon2026
noncomputable section

variable (k : Type) [CommRing k]

/-- Compatible dual numbers have the same constant coefficient. Add their actual
epsilon coefficients while retaining that common original residue. -/
def dualNumberCompatibleAddition :
    CoefficientFiberProduct (TrivSqZeroExt.fstHom k k k).toRingHom
      (TrivSqZeroExt.fstHom k k k).toRingHom →+* DualNumber k where
  toFun x := ⟨x.val.1.fst, x.val.1.snd + x.val.2.snd⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · rfl
    · change (0 : k) + 0 = 0
      exact zero_add 0
  map_zero' := by
    apply TrivSqZeroExt.ext
    · rfl
    · change (0 : k) + 0 = 0
      exact zero_add 0
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · rfl
    · change (x.val.1.snd + y.val.1.snd) + (x.val.2.snd + y.val.2.snd) =
        (x.val.1.snd + x.val.2.snd) + (y.val.1.snd + y.val.2.snd)
      ring
  map_mul' x y := by
    have hx : x.val.1.fst = x.val.2.fst := x.property
    have hy : y.val.1.fst = y.val.2.fst := y.property
    apply TrivSqZeroExt.ext
    · rfl
    · change (x.val.1.fst * y.val.1.snd + x.val.1.snd * y.val.1.fst) +
          (x.val.2.fst * y.val.2.snd + x.val.2.snd * y.val.2.fst) =
        x.val.1.fst * (y.val.1.snd + y.val.2.snd) +
          (x.val.1.snd + x.val.2.snd) * y.val.1.fst
      rw [← hx, ← hy]
      ring

/-- The actual addition coefficient map retains the original residue and adds the
original epsilon values, specifying exactly the coefficient operation used on lifts. -/
theorem dualNumberCompatibleAddition_components
    (x : CoefficientFiberProduct (TrivSqZeroExt.fstHom k k k).toRingHom
      (TrivSqZeroExt.fstHom k k k).toRingHom) :
    (dualNumberCompatibleAddition k x).fst = x.val.1.fst ∧
      (dualNumberCompatibleAddition k x).snd = x.val.1.snd + x.val.2.snd := by
  exact ⟨rfl, rfl⟩

/-- The genuine dual-number algebra map that multiplies epsilon by the original scalar. -/
def dualNumberEpsilonScale (c : k) : DualNumber k →+* DualNumber k :=
  (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom

/-- The original epsilon scaling map fixes the original residue and scales precisely
the first-order coefficient. -/
theorem dualNumberEpsilonScale_components (c : k) (x : DualNumber k) :
    (dualNumberEpsilonScale k c x).fst = x.fst ∧
      (dualNumberEpsilonScale k c x).snd = c * x.snd := by
  constructor
  · exact TrivSqZeroExt.fst_map _ _
  · exact TrivSqZeroExt.snd_map _ _

end
end Dubon2026
