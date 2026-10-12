import Dubon2026.CoinducedShapiroCochains
import Dubon2026.CoinducedSubgroupCoordinates

/-! # The original invariants in the continuous Shapiro comparison

Actual subgroup invariants correspond to constant original coinduced functions.
This degree-zero comparison supplies the H0 side of induced H2/H0 duality in
the DUB-17 finite-module exact-sequence argument.
-/

namespace Dubon2026
noncomputable section

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (S : Subgroup G)

/-- The actual subgroup invariants and actual coinduced invariants are
linearly equivalent by the original constant function and evaluation at one. -/
def coinducedInvariantEquiv :
    (restrictedCoefficientRep A S.subtype).ρ.invariants ≃ₗ[k]
      (Rep.coind S.subtype (Rep.res S.subtype A)).ρ.invariants where
  toFun w := ⟨⟨fun _ => w.val, fun s _ => (w.property s).symm⟩, fun _ => rfl⟩
  invFun f := ⟨f.val.val 1, by
    intro s
    have he := f.val.property s 1
    have ht := congrArg (fun u : Rep.coind S.subtype (Rep.res S.subtype A) => u.val 1)
      (f.property (s : G))
    change f.val.val ((s : G) * 1) = A.ρ (s : G) (f.val.val 1) at he
    change f.val.val (1 * (s : G)) = f.val.val 1 at ht
    rw [mul_one] at he
    rw [one_mul] at ht
    exact he.symm.trans ht⟩
  left_inv _ := rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h := congrArg (fun u : Rep.coind S.subtype (Rep.res S.subtype A) => u.val 1) (f.property g)
    change f.val.val (1 * g) = f.val.val 1 at h
    simpa only [one_mul] using h.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original invariant lift has precisely its actual constant values. -/
theorem coinducedInvariantEquiv_apply
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) (g : G) :
    (coinducedInvariantEquiv A S w).val.val g = w.val := rfl

/-- The degree-zero original Shapiro cochain is exactly the invariant
identification on subgroup invariants, without choosing normalized coset representatives. -/
theorem coinducedShapiroZero_invariant
    (w : (restrictedCoefficientRep A S.subtype).ρ.invariants) :
    coinducedShapiroZero A S w.val = (coinducedInvariantEquiv A S w).val := by
  apply Subtype.ext
  funext t
  change A.ρ t (A.ρ (QuotientGroup.mk t⁻¹ : G ⧸ S).out w.val) = w.val
  rw [← Module.End.mul_apply, ← map_mul]
  have hw : A.ρ (coinducedSubgroupCoordinate S t : G) w.val = w.val :=
    w.property (coinducedSubgroupCoordinate S t)
  rw [coinducedSubgroupCoordinate_val] at hw
  exact hw

end
end Dubon2026
