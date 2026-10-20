import Dubon2026.ParabolicLastRowGroup
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The single scalar quotient of the source last-row parabolic

For DUB-17's BLGG auxiliary family, the final diagonal entry gives a
surjective map to one copy of the residue units. Its kernel is exactly
the last-row condition (0,...,0,1), not the full diagonal torus kernel.
-/

namespace Dubon2026

noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The final scalar entry of the actual last-row parabolic is multiplicative. -/
def parabolicLastRowScalar (a : ι) : parabolicLastRowGroup R a →* R where
  toFun M := M.val.val a a
  map_one' := Matrix.one_apply_eq _
  map_mul' M N := parabolicLastRow_mul_entry a M N.val.val a

/-- The scalar entry is a unit because its domain is the original parabolic group. -/
def parabolicLastRowCharacter (a : ι) : parabolicLastRowGroup R a →* Rˣ :=
  (parabolicLastRowScalar a).toHomUnits

/-- A scalar unit lifts to the original diagonal matrix with all other entries equal to one. -/
def parabolicLastRowDiagonal (a : ι) (u : Rˣ) : parabolicLastRowGroup R a :=
  ⟨Units.map (Matrix.diagonalRingHom ι R).toMonoidHom
      (MulEquiv.piUnits.symm (fun i : ι => if i = a then u else 1)),
    Matrix.blockTriangular_diagonal _⟩

/-- The actual diagonal lift is a section of the source scalar quotient. -/
theorem parabolicLastRowCharacter_diagonal (a : ι) (u : Rˣ) :
    parabolicLastRowCharacter a (parabolicLastRowDiagonal a u) = u := by
  apply Units.ext
  change Matrix.diagonal (fun i : ι => ↑(if i = a then u else 1)) a a = u.val
  simp

/-- The source scalar quotient is surjective on the original parabolic matrices. -/
theorem parabolicLastRowCharacter_surjective (a : ι) :
    Function.Surjective (parabolicLastRowCharacter (R := R) a) :=
  fun u => ⟨parabolicLastRowDiagonal a u, parabolicLastRowCharacter_diagonal a u⟩

/-- The kernel imposes exactly the source's final entry one. -/
theorem parabolicLastRowCharacter_mem_ker_iff (a : ι) (M : parabolicLastRowGroup R a) :
    M ∈ (parabolicLastRowCharacter a).ker ↔ M.val.val a a = 1 := by
  change parabolicLastRowCharacter a M = 1 ↔ _
  rw [Units.ext_iff]
  rfl

/-- The actual parabolic modulo the source kernel is one scalar unit group. -/
def parabolicLastRowQuotientEquiv (a : ι) :
    parabolicLastRowGroup R a ⧸ (parabolicLastRowCharacter a).ker ≃* Rˣ :=
  QuotientGroup.quotientKerEquivOfSurjective _ (parabolicLastRowCharacter_surjective a)

end
end Dubon2026
