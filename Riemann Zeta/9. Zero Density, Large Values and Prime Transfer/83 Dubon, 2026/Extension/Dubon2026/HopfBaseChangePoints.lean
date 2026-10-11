import Dubon2026.AlgebraBaseChangePoints
import Dubon2026.CommutativeHopfPointsCoefficientChange
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Genuine Hopf point groups under scalar extension -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [CommRing F] [Algebra R F]
  [CommRing A] [HopfAlgebra R A] [CommRing K] [Algebra R K] [Algebra F K]
  [IsScalarTower R F K]

/-- The existing algebra base-change equivalence preserves actual convolution multiplication. -/
theorem hopfBaseChangePoint_mul (p q : WithConv (A →ₐ[R] K)) :
    toConv (AlgHom.liftEquiv R F A K (p * q).ofConv) =
      toConv (AlgHom.liftEquiv R F A K p.ofConv) *
        toConv (AlgHom.liftEquiv R F A K q.ofConv) := by
  apply WithConv.ext
  apply (AlgHom.liftEquiv R F A K).symm.injective
  ext a
  simp only [AlgHom.liftEquiv_symm_apply, algebraBaseChangePoint_original]
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  simp only [TensorProduct.comul_tmul, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def]
  generalize Coalgebra.comul (R := R) a = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp [AlgHom.liftEquiv_tmul]
  | add z w hz hw => simp only [map_add, TensorProduct.tmul_add, hz, hw]

/-- The genuine group of points is unchanged by extending the base inside the point field. -/
def hopfBaseChangePointsEquiv :
    WithConv (A →ₐ[R] K) ≃* WithConv (F ⊗[R] A →ₐ[F] K) where
  toFun p := toConv (AlgHom.liftEquiv R F A K p.ofConv)
  invFun p := toConv ((AlgHom.liftEquiv R F A K).symm p.ofConv)
  left_inv p := by
    apply WithConv.ext
    exact (AlgHom.liftEquiv R F A K).symm_apply_apply p.ofConv
  right_inv p := by
    apply WithConv.ext
    exact (AlgHom.liftEquiv R F A K).apply_symm_apply p.ofConv
  map_mul' := hopfBaseChangePoint_mul

/-- The point-group equivalence commutes with the genuine coefficient Galois action. -/
theorem hopfBaseChangePointsEquiv_galois (g : K ≃ₐ[F] K)
    (p : WithConv (A →ₐ[R] K)) :
    hopfBaseChangePointsEquiv (commutativeHopfPointsAutomorphism (g.restrictScalars R) p) =
      commutativeHopfPointsAutomorphism g (hopfBaseChangePointsEquiv p) := by
  apply WithConv.ext
  exact algebraBaseChangePoint_galois g p.ofConv

end
end Dubon2026
