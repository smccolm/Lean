import Dubon2026.SourceBinaryHeckeChange
import Mathlib.RingTheory.TensorProduct.Basic

/-! Tensor coefficient change on the actual native binary H1.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> injection of the original tensor extension into residual H1.
The existing exact coefficient map supplies the literal tensor map.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

private def integralH1CoefficientLinear (R : Type) [CommRing R] (Q w : ℕ) :
    groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w) →ₗ[ℤ]
      groupCohomology.H1 (sourceBinaryCoefficientRep R Q w) where
  toFun := sourceBinaryH1Change (Int.castRingHom R) Q w
  map_add' := map_add _
  map_smul' r x := by
    change sourceBinaryH1Change (Int.castRingHom R) Q w
      ((groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)).isModule.smul r x) = _
    rw [int_smul_eq_zsmul, map_zsmul]
    rfl

/-- The actual integral-to-residue H1 map extended linearly to the tensor product. -/
def sourceBinaryH1TensorChange (R : Type) [CommRing R] (Q w : ℕ) :
    R ⊗[ℤ] groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w) →ₗ[R]
      groupCohomology.H1 (sourceBinaryCoefficientRep R Q w) :=
  (integralH1CoefficientLinear R Q w).liftBaseChange R

/-- The tensor map sends a pure tensor to the actual scalar multiple of coefficient reduction. -/
theorem sourceBinaryH1TensorChange_tmul (R : Type) [CommRing R] (Q w : ℕ)
    (a : R) (x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1TensorChange R Q w (a ⊗ₜ[ℤ] x) =
      a • sourceBinaryH1Change (Int.castRingHom R) Q w x := rfl

/-- Every integral cocycle has the literal coefficient-transformed representative after tensor change. -/
theorem sourceBinaryH1TensorChange_cocycle (R : Type) [CommRing R] (Q w : ℕ)
    (a : R) (z : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1TensorChange R Q w (a ⊗ₜ[ℤ] groupCohomology.H1π _ z) =
      groupCohomology.H1π _ (a • sourceBinaryCocyclesChange (Int.castRingHom R) Q w z) := by
  rw [sourceBinaryH1TensorChange_tmul, sourceBinaryH1Change_cocycle, map_smul]

/-- The full actual Hecke correspondence commutes with the tensor coefficient map. -/
theorem sourceBinaryH1TensorChange_hecke (R : Type) [CommRing R] (Q w p : ℕ)
    [NeZero p] (hp : p.Prime)
    (x : R ⊗[ℤ] groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryH1TensorChange R Q w ((sourceBinaryHeckeH1 ℤ (Q := Q) hp w).baseChange R x) =
      sourceBinaryHeckeH1 R hp w (sourceBinaryH1TensorChange R Q w x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, sourceBinaryH1TensorChange_tmul,
      sourceBinaryH1Change_hecke, sourceBinaryH1TensorChange_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end
end Dubon2026
