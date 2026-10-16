import Dubon2026.ArithmeticOrbitLocalField

/-! # Finite indexing for the actual arithmetic Mackey sum

The original finite arithmetic field fixes an open subgroup of the
compact arithmetic group. Its cosets and their local orbit quotient
are therefore finite. These constructed instances discharge the finite
index premises in DUB-17's prime-indexed invariant-sum assembly.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The actual global coset space is finite by openness of the original field's fixing subgroup. -/
local instance arithmeticOrbitGlobalCosetsFinite :
    Finite (rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :=
  Subgroup.quotient_finite_of_isOpen (rationalArithmeticOrbitFixingSubgroup a F) F.fixingSubgroup_isOpen

/-- Enumerate the actual finite global coset space. -/
local instance arithmeticOrbitGlobalCosetsFintype :
    Fintype (rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) := Fintype.ofFinite _

/-- The exact local Mackey orbit quotient is finite as a quotient of those same global cosets. -/
local instance arithmeticOrbitIndexFinite :
    Finite (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F)) :=
  Finite.of_surjective
    (fun c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F =>
      (Quotient.mk'' c : cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalArithmeticOrbitFixingSubgroup a F)))
    (fun ω => Quotient.inductionOn' ω (fun c => ⟨c, rfl⟩))

/-- Enumerate the exact finite local Mackey orbit quotient. -/
local instance arithmeticOrbitIndexFintype :
    Fintype (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F)) := Fintype.ofFinite _

end
end Dubon2026
