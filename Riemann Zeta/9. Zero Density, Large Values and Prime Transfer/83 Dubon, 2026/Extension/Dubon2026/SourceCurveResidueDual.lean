import Dubon2026.SourceCurveLocalDifferentials
import Mathlib.LinearAlgebra.Dual.Defs

/-! The dual used by the local residue derivation. Field elements act by
precomposition with multiplication, so the residue Leibniz rule becomes the
literal derivation rule. This exact action is needed for the differential
chain rule; the usual pointwise scalar action would not model it. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The constant-field dual, carrying the function-field action by precomposition. -/
def ResidueDual := F →ₗ[K] K

/-- The additive group of the literal linear functionals. -/
instance residueDualAddCommGroup : AddCommGroup (ResidueDual K F) :=
  inferInstanceAs (AddCommGroup (F →ₗ[K] K))

/-- Constant scalars act pointwise on the dual. -/
instance residueDualKModule : Module K (ResidueDual K F) :=
  inferInstanceAs (Module K (F →ₗ[K] K))

/-- The underlying constant-field linear map. -/
def residueDualLinearMap (φ : ResidueDual K F) : F →ₗ[K] K := φ

variable {K F}

/-- Equality of residue-dual elements is equality of all their evaluations. -/
theorem residueDual_ext {φ ψ : ResidueDual K F}
    (h : ∀ x, residueDualLinearMap K F φ x = residueDualLinearMap K F ψ x) : φ = ψ :=
  LinearMap.ext h

/-- Function-field scalars act on the argument of a linear functional. -/
instance residueDualFModule : Module F (ResidueDual K F) where
  smul h φ := residueDualLinearMap K F φ ∘ₗ Algebra.lmul K F h
  one_smul φ := residueDual_ext fun x => by
    change (residueDualLinearMap K F φ) (1 * x) = _
    rw [one_mul]
  mul_smul a b φ := residueDual_ext fun x => by
    change (residueDualLinearMap K F φ) ((a * b) * x) =
      (residueDualLinearMap K F φ) (b * (a * x))
    rw [mul_comm a b, mul_assoc]
  smul_zero _ := residueDual_ext fun _ => rfl
  smul_add _ _ _ := residueDual_ext fun _ => rfl
  add_smul a b φ := residueDual_ext fun x => by
    change (residueDualLinearMap K F φ) ((a + b) * x) = _
    rw [add_mul, map_add]
    rfl
  zero_smul φ := residueDual_ext fun x => by
    change (residueDualLinearMap K F φ) (0 * x) = 0
    rw [zero_mul, map_zero]

/-- Evaluation of the function-field action. -/
theorem residueDual_smul_apply (h : F) (φ : ResidueDual K F) (x : F) :
    residueDualLinearMap K F (h • φ) x = residueDualLinearMap K F φ (h * x) := rfl

/-- Evaluation of the constant-field action. -/
theorem residueDual_ksmul_apply (c : K) (φ : ResidueDual K F) (x : F) :
    residueDualLinearMap K F (c • φ) x = c • residueDualLinearMap K F φ x := rfl

/-- The pointwise constant action and precomposition field action agree as a scalar tower. -/
instance residueDualScalarTower : IsScalarTower K F (ResidueDual K F) where
  smul_assoc c h φ := residueDual_ext fun x => by
    change residueDualLinearMap K F φ ((c • h) * x) =
      c • residueDualLinearMap K F φ (h * x)
    rw [smul_mul_assoc, map_smul]

end Dubon2026.SourceCurve.ResidueTrace
