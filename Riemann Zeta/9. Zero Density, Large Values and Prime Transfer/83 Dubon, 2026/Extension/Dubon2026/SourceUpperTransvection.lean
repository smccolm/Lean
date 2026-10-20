import Dubon2026.SourceSquareZeroLine
import Dubon2026.GeneralLinearBorelCharacter

/-! Original elementary upper-unipotent matrices over every coefficient algebra.
These exact matrices connect the source infinitesimal invariants with
the all-algebra invariance required by the proved highest-line theorem.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The actual elementary matrix over the original coefficient ring. -/
def sourceUpperTransvection {i j : Fin n} (hij : i ≠ j) (t : R) :
    GeneralLinearGroup (Fin n) R :=
  sourceSquareZeroLine (Matrix.single i j (1 : R))
    (by rw [Matrix.single_mul_single_of_ne (h := hij.symm)]) t

/-- The original elementary matrix is the literal native transvection. -/
theorem sourceUpperTransvection_coe {i j : Fin n} (hij : i ≠ j) (t : R) :
    (sourceUpperTransvection hij t).val = Matrix.transvection i j t := by
  change 1 + t • Matrix.single i j (1 : R) = 1 + Matrix.single i j t
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

/-- An elementary upper-unipotent matrix belongs to the original Borel subgroup over every coefficient algebra. -/
theorem sourceUpperTransvection_mem_borel {i j : Fin n} (hij : i < j) (t : R) :
    sourceUpperTransvection hij.ne t ∈ generalLinearBorel R n := by
  change (sourceUpperTransvection hij.ne t).val.BlockTriangular id
  rw [sourceUpperTransvection_coe]
  intro a b hab
  change b < a at hab
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hab.ne']
  simp only [zero_add, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (not_lt_of_ge hij.le hab).elim
  · rfl

end
end Dubon2026
