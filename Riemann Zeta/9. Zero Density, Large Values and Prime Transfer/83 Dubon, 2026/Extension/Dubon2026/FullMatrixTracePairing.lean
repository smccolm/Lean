import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.Matrix.Basis

/-! # The actual perfect trace pairing on the full original matrix algebra -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The genuine matrix trace pairing as a linear map into the actual module dual. -/
def fullMatrixTracePairing : Matrix ι ι R →ₗ[R] Module.Dual R (Matrix ι ι R) where
  toFun X :=
    { toFun := fun Y => Matrix.trace (X * Y)
      map_add' := fun Y Z => by rw [mul_add, Matrix.trace_add]
      map_smul' := fun r Y => by rw [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply] }
  map_add' X Z := by
    ext Y
    exact (congrArg Matrix.trace (add_mul X Z Y)).trans (Matrix.trace_add _ _)
  map_smul' r X := by
    ext Y
    exact (congrArg Matrix.trace (Matrix.smul_mul r X Y)).trans (Matrix.trace_smul r _)

/-- Every linear functional on the original full matrix algebra is represented by an actual matrix under the trace pairing; its entries are the functional's values on the transposed matrix units. -/
theorem fullMatrixTracePairing_coordinates
    (f : Module.Dual R (Matrix ι ι R)) (Y : Matrix ι ι R) :
    Matrix.trace (Matrix.of (fun i j => f (Matrix.single j i 1)) * Y) = f Y := by
  have hf : f Y = ∑ i, ∑ j, Y i j * f (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : R) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_eq_mul]
  rw [hf]
  change (∑ i, ∑ j, f (Matrix.single j i 1) * Y j i) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The original full-matrix trace pairing is bijective over every original commutative coefficient ring. -/
theorem fullMatrixTracePairing_bijective :
    Function.Bijective (fullMatrixTracePairing (ι := ι) (R := R)) := by
  constructor
  · intro X Y h
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Z
    exact DFunLike.congr_fun h Z
  · intro f
    refine ⟨Matrix.of (fun i j => f (Matrix.single j i 1)), ?_⟩
    ext Y
    exact fullMatrixTracePairing_coordinates f Y

/-- The actual matrix trace pairing identifies the full original matrix algebra with its genuine module dual. -/
def fullMatrixTraceDuality : Matrix ι ι R ≃ₗ[R] Module.Dual R (Matrix ι ι R) :=
  LinearEquiv.ofBijective fullMatrixTracePairing fullMatrixTracePairing_bijective

end
end Dubon2026
