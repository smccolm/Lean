import Dubon2026.FiniteFreeHopfGaloisAction
import Dubon2026.HopfTensorPointsProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Original finite-free point products and their Galois compatibility -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B F K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [HopfAlgebra R B] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]

/-- Restriction along the original coordinate map commutes with the actual original Galois point actions. -/
theorem hopfPointsRestriction_galois (h : A →ₐc[R] B) (g : K ≃ₐ[F] K)
    (p : WithConv (B →ₐ[R] K)) :
    hopfPointsRestriction h (hopfPointsGaloisAction (R := R) g p) =
      hopfPointsGaloisAction (R := R) g (hopfPointsRestriction h p) := by
  apply WithConv.ext
  ext a
  rfl

/-- The tensor-coordinate product equivalence preserves the original Galois action on each original point factor. -/
theorem hopfTensorPointsProductEquiv_galois (g : K ≃ₐ[F] K)
    (p : WithConv ((A ⊗[R] B) →ₐ[R] K)) :
    hopfTensorPointsProductEquiv (hopfPointsGaloisAction (R := R) g p) =
      (hopfPointsGaloisAction (R := R) g (hopfTensorPointsProductEquiv p).1,
       hopfPointsGaloisAction (R := R) g (hopfTensorPointsProductEquiv p).2) := by
  apply Prod.ext
  · apply WithConv.ext
    apply AlgHom.ext
    intro a
    rfl
  · apply WithConv.ext
    apply AlgHom.ext
    intro b
    rfl

/-- Finite free original coordinate algebras give a finite free actual tensor-coordinate algebra for their group-scheme product. -/
theorem hopfTensorCoordinates_finite_free
    [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] :
    Module.Finite R (A ⊗[R] B) ∧ Module.Free R (A ⊗[R] B) := by
  exact ⟨inferInstance, inferInstance⟩

end
end Dubon2026
