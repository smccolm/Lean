import Dubon2026.ParabolicLastRowQuotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # The source auxiliary U0 and U1 over the original local ring

For DUB-17, BLGG's local U0 reduces to last row (0,...,0,*).
Its quotient by U1 is constructed from the original residue map, with
surjectivity proved by lifting scalar residue units and diagonal matrices.
-/

namespace Dubon2026

noncomputable section

open IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original local integral matrices reducing to the source last-row parabolic. -/
def parabolicResidueLevelZero (a : ι) : Subgroup (Matrix ι ι R)ˣ :=
  (parabolicLastRowGroup (ResidueField R) a).comap
    (Units.map (residue R).mapMatrix.toMonoidHom)

/-- Reduction of U0 lands in the actual residue parabolic. -/
def parabolicResidueReduction (a : ι) :
    parabolicResidueLevelZero R a →* parabolicLastRowGroup (ResidueField R) a where
  toFun M := ⟨(show (Matrix ι ι R)ˣ →* (Matrix ι ι (ResidueField R))ˣ from
    Units.map (residue R).mapMatrix.toMonoidHom) M.val, M.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The original auxiliary scalar character, one residue-unit factor per place. -/
def parabolicResidueCharacter (a : ι) : parabolicResidueLevelZero R a →* (ResidueField R)ˣ :=
  (parabolicLastRowCharacter a).comp (parabolicResidueReduction R a)

/-- Membership in U0 is precisely the printed row congruence. -/
theorem parabolicResidueLevelZero_mem_iff (a : ι) (M : (Matrix ι ι R)ˣ) :
    M ∈ parabolicResidueLevelZero R a ↔ ∀ j, j ≠ a → residue R (M.val a j) = 0 :=
  parabolicLastRowGroup_mem_iff a _

/-- The character is the original residue of the last diagonal coefficient. -/
theorem parabolicResidueCharacter_val (a : ι) (M : parabolicResidueLevelZero R a) :
    (parabolicResidueCharacter R a M).val = residue R (M.val.val a a) := rfl

/-- Lift an original local unit to a diagonal element of the actual residue level U0. -/
def parabolicResidueDiagonal (a : ι) (u : Rˣ) : parabolicResidueLevelZero R a :=
  ⟨(parabolicLastRowDiagonal a u).val, by
    change ((residue R).mapMatrix (parabolicLastRowDiagonal a u).val.val).BlockTriangular
      (fun i => if i = a then (1 : ℕ) else 0)
    exact (parabolicLastRowDiagonal a u).property.map (residue R)⟩

/-- The diagonal lift has precisely the expected scalar residue character. -/
theorem parabolicResidueCharacter_diagonal (a : ι) (u : Rˣ) :
    parabolicResidueCharacter R a (parabolicResidueDiagonal R a u) =
      Units.map (residue R).toMonoidHom u := by
  apply Units.ext
  rw [parabolicResidueCharacter_val]
  change residue R (Matrix.diagonal (fun i : ι => ↑(if i = a then u else 1)) a a) = _
  simp

/-- The actual residue character is surjective; no full matrix lifting is assumed. -/
theorem parabolicResidueCharacter_surjective (a : ι) :
    Function.Surjective (parabolicResidueCharacter R a) := by
  intro u
  obtain ⟨v, hv⟩ := surjective_units_map_of_local_ringHom (residue R)
    residue_surjective inferInstance u
  exact ⟨parabolicResidueDiagonal R a v, (parabolicResidueCharacter_diagonal R a v).trans hv⟩

/-- The original local U1 inside U0 is the kernel of the one scalar residue character. -/
abbrev parabolicResidueLevelOne (a : ι) : Subgroup (parabolicResidueLevelZero R a) :=
  (parabolicResidueCharacter R a).ker

/-- U1 imposes exactly the source's final residue entry one. -/
theorem parabolicResidueLevelOne_mem_iff (a : ι) (M : parabolicResidueLevelZero R a) :
    M ∈ parabolicResidueLevelOne R a ↔ residue R (M.val.val a a) = 1 := by
  change parabolicResidueCharacter R a M = 1 ↔ _
  rw [Units.ext_iff]
  rfl

/-- The actual local U0/U1 is the single residue-unit group in the source auxiliary family. -/
def parabolicResidueQuotientEquiv (a : ι) :
    parabolicResidueLevelZero R a ⧸ parabolicResidueLevelOne R a ≃* (ResidueField R)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective _ (parabolicResidueCharacter_surjective R a)

end
end Dubon2026
