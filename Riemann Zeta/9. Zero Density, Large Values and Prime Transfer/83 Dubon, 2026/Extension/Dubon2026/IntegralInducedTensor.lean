import Dubon2026.IntegralInducedFiniteFree
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! Geraghty Definition 2.2.3's actual tensor of the integral induced modules.
The individual factors are the literal regular-function modules, and their
finite freeness is proved rather than supplied. The action is the tensor
of their original right translations. Arithmetic embedding maps into the
local general linear factors are a separate source specialization.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

universe u
variable (R : Type u) [CommRing R] {I : Type u} (n : ℕ)
  (lam : I → Fin n → ℤ)

/-- The original integral coefficient module is the tensor of the literal induced modules indexed by the source embeddings. -/
def IntegralInducedTensor :=
  ⨂[R] i : I, generalLinearIntegralInducedSubmodule R n (lam i)

/-- The source tensor carries its native additive group structure. The named instance keeps later concrete coefficient specializations small. -/
instance integralInducedTensorAddCommGroup : AddCommGroup (IntegralInducedTensor R n lam) :=
  inferInstanceAs (AddCommGroup (⨂[R] i : I, generalLinearIntegralInducedSubmodule R n (lam i)))

/-- The source tensor carries precisely the original native tensor scalar action. -/
instance integralInducedTensorModule : Module R (IntegralInducedTensor R n lam) :=
  inferInstanceAs (Module R (⨂[R] i : I, generalLinearIntegralInducedSubmodule R n (lam i)))

/-- The tensor coefficient action applies each factor's original right translation. -/
def integralInducedTensorRepresentation :
    Representation R (I → Matrix.GeneralLinearGroup (Fin n) R)
      (IntegralInducedTensor R n lam) :=
  { toFun := fun g => PiTensorProduct.map
      (fun i => generalLinearIntegralInducedRepresentation R n (lam i) (g i))
    map_one' := by
      simp
      rfl
    map_mul' := by
      intro g h
      simp only [Pi.mul_apply, map_mul]
      exact PiTensorProduct.map_mul _ _ }

/-- The action on actual pure tensors is exactly the source tensor of right translations. -/
theorem integralInducedTensorRepresentation_tprod
    (g : I → Matrix.GeneralLinearGroup (Fin n) R)
    (p : ∀ i, generalLinearIntegralInducedSubmodule R n (lam i)) :
    integralInducedTensorRepresentation R n lam g (PiTensorProduct.tprod R p) =
      PiTensorProduct.tprod R
        (fun i => generalLinearIntegralInducedRepresentation R n (lam i) (g i) (p i)) :=
  PiTensorProduct.map_tprod _ _

variable [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] [CharZero R]
  [Finite I]

/-- A basis of the actual embedding tensor product, constructed from the proved finite-free original induced factors. -/
def integralLocalInducedTensorBasis {m : ℕ} (weight : I → Fin (m + 1) → ℤ) :
    Module.Basis
      (∀ i, Module.Free.ChooseBasisIndex R
        (generalLinearIntegralInducedSubmodule R (m + 1) (weight i))) R
      (IntegralInducedTensor R (m + 1) weight) :=
  Basis.piTensorProduct fun i =>
    Module.Free.chooseBasis R (generalLinearIntegralInducedSubmodule R (m + 1) (weight i))

/-- Finite generation of the source tensor module is derived from its actual finite factor bases. -/
instance integralLocalInducedTensorFinite {m : ℕ} (weight : I → Fin (m + 1) → ℤ) :
    Module.Finite R (IntegralInducedTensor R (m + 1) weight) :=
  Module.Finite.of_basis (integralLocalInducedTensorBasis R weight)

/-- Freeness of the source tensor module is derived from its actual factor bases. -/
instance integralLocalInducedTensorFree {m : ℕ} (weight : I → Fin (m + 1) → ℤ) :
    Module.Free R (IntegralInducedTensor R (m + 1) weight) :=
  Module.Free.of_basis (integralLocalInducedTensorBasis R weight)

/-- The literal source tensor coefficient module is finite free without an assumed representation lattice. -/
theorem integralLocalInducedTensor_finite_free {m : ℕ} (weight : I → Fin (m + 1) → ℤ) :
    Module.Finite R (IntegralInducedTensor R (m + 1) weight) ∧
      Module.Free R (IntegralInducedTensor R (m + 1) weight) :=
  ⟨inferInstance, inferInstance⟩

end
end Dubon2026
