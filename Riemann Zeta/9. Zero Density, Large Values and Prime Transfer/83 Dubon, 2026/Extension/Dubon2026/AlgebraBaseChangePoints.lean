import Mathlib.RingTheory.TensorProduct.Basic

/-! # Actual algebra points under scalar extension -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [CommRing F] [Algebra R F]
  [CommRing A] [Algebra R A] [CommRing K] [Algebra R K] [Algebra F K]
  [IsScalarTower R F K]

/-- The actual scalar-extension point is evaluated on the original tensor coordinates. -/
theorem algebraBaseChangePoint_tmul (p : A →ₐ[R] K) (s : F) (a : A) :
    AlgHom.liftEquiv R F A K p (s ⊗ₜ[R] a) = algebraMap F K s * p a := by
  rw [AlgHom.liftEquiv_tmul, Algebra.smul_def]

/-- Restriction of the actual scalar-extension point recovers every original coordinate value. -/
theorem algebraBaseChangePoint_original (p : A →ₐ[R] K) (a : A) :
    AlgHom.liftEquiv R F A K p (1 ⊗ₜ[R] a) = p a := by
  rw [AlgHom.liftEquiv_tmul, one_smul]

/-- Scalar extension of actual points commutes with every coefficient automorphism fixing the extension field. -/
theorem algebraBaseChangePoint_galois (g : K ≃ₐ[F] K) (p : A →ₐ[R] K) :
    AlgHom.liftEquiv R F A K ((g.restrictScalars R).toAlgHom.comp p) =
      g.toAlgHom.comp (AlgHom.liftEquiv R F A K p) := by
  apply Algebra.TensorProduct.ext_ring
  ext a
  change AlgHom.liftEquiv R F A K ((g.restrictScalars R).toAlgHom.comp p)
    (1 ⊗ₜ[R] a) = g (AlgHom.liftEquiv R F A K p (1 ⊗ₜ[R] a))
  simp only [AlgHom.liftEquiv_tmul, one_smul]
  rfl

end
end Dubon2026
