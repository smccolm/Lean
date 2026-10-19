import Dubon2026.PolarizedSwitch
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The group of coefficient-ring points of CHT Section 2.1's polarized target
G_n, built using the existing semidirect-product construction. Its multiplier
fixes the similitude rather than the determinant of the GL_n component. This
is the target required for the CM deformation comparison in DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The order-two group acts by the exact CHT switching involution. -/
def polarizedSwitchAction : Multiplicative (ZMod 2) →* MulAut (GeneralLinearGroup ι R × Rˣ) where
  toFun z := if z.toAdd = 0 then 1 else polarizedSwitchAut
  map_one' := by simp
  map_mul' z w := by
    change (if z.toAdd + w.toAdd = (0 : ZMod 2) then 1 else polarizedSwitchAut) =
      (if z.toAdd = 0 then 1 else polarizedSwitchAut) *
        (if w.toAdd = 0 then 1 else polarizedSwitchAut)
    generalize z.toAdd = a
    generalize w.toAdd = b
    fin_cases a <;> fin_cases b
    · change (1 : MulAut (GeneralLinearGroup ι R × Rˣ)) = 1 * 1
      exact (one_mul 1).symm
    · change polarizedSwitchAut = 1 * polarizedSwitchAut
      exact (one_mul _).symm
    · change polarizedSwitchAut = polarizedSwitchAut * 1
      exact (mul_one _).symm
    · change 1 = polarizedSwitchAut * polarizedSwitchAut
      rw [← pow_two, polarizedSwitchAut_sq]

/-- Switching preserves the multiplier coordinate. -/
theorem polarizedSwitchAction_multiplier (z : Multiplicative (ZMod 2))
    (x : GeneralLinearGroup ι R × Rˣ) : (polarizedSwitchAction z x).2 = x.2 := by
  change ((if z.toAdd = 0 then (1 : MulAut (GeneralLinearGroup ι R × Rˣ))
    else polarizedSwitchAut) x).2 = x.2
  split_ifs <;> rfl

/-- The source's actual disconnected polarized group over the coefficient ring. -/
abbrev PolarizedGaloisGroup (ι R : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :=
  SemidirectProduct (GeneralLinearGroup ι R × Rˣ) (Multiplicative (ZMod 2)) polarizedSwitchAction

/-- The original identity-component inclusion. -/
def polarizedIdentityComponent : GeneralLinearGroup ι R × Rˣ →* PolarizedGaloisGroup ι R :=
  SemidirectProduct.inl

/-- The source involution j. -/
def polarizedComplexConjugation : PolarizedGaloisGroup ι R :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

/-- The exact component homomorphism of the polarized group. -/
def polarizedComponent : PolarizedGaloisGroup ι R →* Multiplicative (ZMod 2) :=
  SemidirectProduct.rightHom

/-- Its identity component is the kernel of its component homomorphism. -/
theorem polarizedIdentityComponent_range :
    (polarizedIdentityComponent (ι := ι) (R := R)).range = polarizedComponent.ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

/-- The component sign used in the source's similitude character. -/
def polarizedComponentSign : Multiplicative (ZMod 2) →* Rˣ where
  toFun z := if z.toAdd = 0 then 1 else -1
  map_one' := by simp
  map_mul' z w := by
    change (if z.toAdd + w.toAdd = (0 : ZMod 2) then (1 : Rˣ) else -1) =
      (if z.toAdd = 0 then 1 else -1) * (if w.toAdd = 0 then 1 else -1)
    generalize z.toAdd = a
    generalize w.toAdd = b
    fin_cases a <;> fin_cases b
    · change (1 : Rˣ) = 1 * 1
      exact (one_mul 1).symm
    · change (-1 : Rˣ) = 1 * -1
      exact (one_mul _).symm
    · change (-1 : Rˣ) = -1 * 1
      exact (mul_one _).symm
    · change (1 : Rˣ) = -1 * -1
      simp

/-- The source multiplier sends (g,mu) to mu and j to minus one. -/
def polarizedSimilitude : PolarizedGaloisGroup ι R →* Rˣ where
  toFun x := x.left.2 * polarizedComponentSign x.right
  map_one' := by simp
  map_mul' x y := by
    change (x.left.2 * (polarizedSwitchAction x.right y.left).2) *
      polarizedComponentSign (x.right * y.right) = _
    rw [polarizedSwitchAction_multiplier, map_mul]
    exact mul_mul_mul_comm _ _ _ _

/-- The multiplier has its exact source value on the identity component. -/
theorem polarizedSimilitude_identityComponent (x : GeneralLinearGroup ι R × Rˣ) :
    polarizedSimilitude (polarizedIdentityComponent x) = x.2 := by
  simp [polarizedSimilitude, polarizedIdentityComponent]

/-- The multiplier has its exact source sign on j. -/
theorem polarizedSimilitude_complexConjugation :
    polarizedSimilitude (polarizedComplexConjugation (ι := ι) (R := R)) = -1 := by
  simp [polarizedSimilitude, polarizedComplexConjugation, polarizedComponentSign]

end Dubon2026
