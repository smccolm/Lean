import Dubon2026.SubmoduleCoordinateLineSplitting
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.FinCases

/-! # A genuine rank-one invariant direct summand contains an original primitive vector -/

namespace Dubon2026
noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A vector on which an actual original linear functional has value one has a genuine unit coordinate over the original local ring. -/
theorem vectorTwo_exists_unit_coordinate_of_dual_one
    (f : (Fin 2 → R) →ₗ[R] R) (v : Fin 2 → R) (hv : f v = 1) :
    ∃ i, IsUnit (v i) := by
  have he : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  have hsum : v 0 * f (Pi.single 0 1) + v 1 * f (Pi.single 1 1) = 1 := by
    calc
      _ = f (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1) := by simp
      _ = f v := congrArg f he.symm
      _ = 1 := hv
  have hu : IsUnit (v 0 * f (Pi.single 0 1) + v 1 * f (Pi.single 1 1)) :=
    hsum.symm ▸ isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact ⟨0, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨1, isUnit_of_mul_isUnit_left h⟩

/-- An actual free rank-one direct summand of the original two-dimensional local coefficient module has a genuine primitive vector in that same submodule. -/
theorem submodule_rankOne_exists_primitive_vector
    (S N : Submodule R (Fin 2 → R)) (hSN : IsCompl S N) (e : S ≃ₗ[R] R) :
    ∃ v : Fin 2 → R, v ∈ S ∧ ∃ i, IsUnit (v i) := by
  let x : S := e.symm 1
  let f : (Fin 2 → R) →ₗ[R] R := e.toLinearMap.comp (S.projectionOnto N hSN)
  have hx : f x.val = 1 := by
    change e (S.projectionOnto N hSN x) = 1
    rw [Submodule.projectionOnto_apply_left]
    exact e.apply_symm_apply 1
  exact ⟨x.val, x.property, vectorTwo_exists_unit_coordinate_of_dual_one f x.val hx⟩

end
end Dubon2026
