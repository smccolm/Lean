import Dubon2026.AlgebraIdempotentLeftIdeal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The actual original algebra action on its idempotent left ideal and its whole matrix representation -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι S A : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing S] [Ring A] [Algebra S A]

/-- Genuine left multiplication by the original algebra acts linearly on its actual idempotent left ideal. -/
def algebraIdempotentLeftAction (e : A) :
    A →* Module.End S (algebraIdempotentLeftIdeal (S := S) e) where
  toFun a :=
    { toFun := fun x => ⟨a * x.val, mul_mem_algebraIdempotentLeftIdeal e a x.val x.property⟩
      map_add' x y := Subtype.ext (mul_add a x.val y.val)
      map_smul' c x := Subtype.ext (Algebra.mul_smul_comm c a x.val) }
  map_one' := by
    ext x
    exact one_mul x.val
  map_mul' a b := by
    ext x
    exact mul_assoc a b x.val

/-- The constructed left action evaluates to the actual original algebra product. -/
theorem algebraIdempotentLeftAction_val (e a : A)
    (x : algebraIdempotentLeftIdeal (S := S) e) :
    (algebraIdempotentLeftAction e a x).val = a * x.val := rfl

/-- Express the whole original group action on the actual left ideal in its genuine coefficient basis. Inverses come from the original group law. -/
def algebraIdempotentMatrixRepresentation (σ : G →* A) (e : A)
    (b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e)) :
    G →* GeneralLinearGroup ι S :=
  (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp
    ((algebraIdempotentLeftAction e).comp σ)).toHomUnits

/-- The whole constructed matrix is the matrix of actual original left multiplication in the same basis. -/
theorem algebraIdempotentMatrixRepresentation_val (σ : G →* A) (e : A)
    (b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e)) (g : G) :
    (algebraIdempotentMatrixRepresentation σ e b g).val =
      LinearMap.toMatrix b b (algebraIdempotentLeftAction e (σ g)) := rfl

/-- Each genuine coefficient of the constructed whole representation is the actual original left-ideal basis coordinate. -/
theorem algebraIdempotentMatrixRepresentation_apply (σ : G →* A) (e : A)
    (b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e)) (g : G) (i j : ι) :
    (algebraIdempotentMatrixRepresentation σ e b g).val i j =
      b.repr (algebraIdempotentLeftAction e (σ g) (b j)) i := by
  rw [algebraIdempotentMatrixRepresentation_val, LinearMap.toMatrix_apply]

end
end Dubon2026
