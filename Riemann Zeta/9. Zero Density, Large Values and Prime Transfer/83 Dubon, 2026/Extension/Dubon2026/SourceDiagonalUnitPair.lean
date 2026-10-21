import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Group.Pi.Units

/-! DUB-17/18 -> residual Galois association -> boundary character branch.
The two actual unit characters give a genuine invertible rank-two matrix
representation. Adapted from the diagonal part of the archived
Apache-2.0 anthropics/fermats-last-theorem revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom.
-/
namespace Dubon2026
noncomputable section
open Matrix
variable {G F : Type*} [Group G] [CommRing F]

private def pairUnits (a b : G →* Fˣ) : G →* (Fin 2 → F)ˣ :=
  (MulEquiv.piUnits (M := fun _ : Fin 2 => F)).symm.toMonoidHom.comp
    (Pi.monoidHom (fun i : Fin 2 => Fin.cases a (fun _ => b) i))

/-- The genuine diagonal representation of two unit characters. -/
def sourceDiagonalUnitPair (a b : G →* Fˣ) : G →* GeneralLinearGroup (Fin 2) F :=
  (Units.map (Matrix.diagonalRingHom (Fin 2) F).toMonoidHom).comp (pairUnits a b)

/-- The diagonal representation has exactly the two original characters
as its matrix entries. -/
theorem sourceDiagonalUnitPair_val (a b : G →* Fˣ) (g : G) :
    (sourceDiagonalUnitPair a b g).val =
      Matrix.diagonal (fun i : Fin 2 => Fin.cases (a g : F) (fun _ => (b g : F)) i) := by
  change Matrix.diagonal ((pairUnits a b g).val) = _
  congr 1
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

/-- The trace is the sum of the two original characters. -/
theorem sourceDiagonalUnitPair_trace (a b : G →* Fˣ) (g : G) :
    Matrix.trace (sourceDiagonalUnitPair a b g).val = (a g : F) + (b g : F) := by
  rw [sourceDiagonalUnitPair_val, Matrix.trace_diagonal, Fin.sum_univ_two]
  rfl

/-- The determinant is the product of the two original characters. -/
theorem sourceDiagonalUnitPair_det (a b : G →* Fˣ) (g : G) :
    Matrix.det (sourceDiagonalUnitPair a b g).val = (a g : F) * (b g : F) := by
  rw [sourceDiagonalUnitPair_val, Matrix.det_diagonal, Fin.prod_univ_two]
  rfl

/-- If both original characters kill an element, the full matrix does too. -/
theorem sourceDiagonalUnitPair_eq_one (a b : G →* Fˣ) (g : G)
    (ha : a g = 1) (hb : b g = 1) : sourceDiagonalUnitPair a b g = 1 := by
  apply Units.ext
  rw [sourceDiagonalUnitPair_val, Units.val_one]
  have h : (fun i : Fin 2 => Fin.cases (a g : F) (fun _ => (b g : F)) i) =
      (1 : Fin 2 → F) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i
    · change (a g : F) = 1
      rw [ha, Units.val_one]
    · change (b g : F) = 1
      rw [hb, Units.val_one]
  rw [h]
  exact Matrix.diagonal_one

end
end Dubon2026
