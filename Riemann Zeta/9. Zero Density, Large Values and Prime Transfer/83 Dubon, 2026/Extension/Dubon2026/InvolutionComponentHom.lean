import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Reuse the existing integer-to-cyclic quotient lift for the order-two
real-place action. This supplies the component homomorphism of the actual
polarized matrix involution in DUB-17. -/

namespace Dubon2026

variable {T : Type*} [Group T]

/-- An actual involution induces a component homomorphism through Mathlib's cyclic quotient. -/
def involutionComponentHom (t : T) (ht : t ^ 2 = 1) : Multiplicative (ZMod 2) →* T :=
  (ZMod.lift 2 ⟨(zpowersHom T t).toAdditive, by
    change t ^ (2 : ℤ) = 1
    simpa only [zpow_ofNat] using ht⟩).toMultiplicative

/-- The nontrivial component is sent to the original involution. -/
theorem involutionComponentHom_generator (t : T) (ht : t ^ 2 = 1) :
    involutionComponentHom t ht (Multiplicative.ofAdd (1 : ZMod 2)) = t := by
  change (ZMod.lift 2 ⟨(zpowersHom T t).toAdditive, by
    change t ^ (2 : ℤ) = 1
    simpa only [zpow_ofNat] using ht⟩) (1 : ZMod 2) = Additive.ofMul t
  rw [← Int.cast_one, ZMod.lift_coe]
  exact zpow_one t

end Dubon2026
