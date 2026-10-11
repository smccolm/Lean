import Dubon2026.CommutativeHopfPointsGroup

/-! # Genuine coefficient changes on the actual Hopf-algebra points -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B C : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- A coefficient algebra homomorphism acts on actual points by composition and preserves the existing convolution multiplication. -/
def commutativeHopfPointsMap (f : B →ₐ[R] C) :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] C) where
  toFun p := toConv (f.comp p.ofConv)
  map_one' := by
    apply WithConv.ext
    ext a
    exact f.commutes _
  map_mul' p q := by
    apply WithConv.ext
    exact AlgHom.comp_convMul_distrib f p q

/-- The coefficient map uses the value of the same original point on every coordinate. -/
theorem commutativeHopfPointsMap_apply (f : B →ₐ[R] C)
    (p : WithConv (A →ₐ[R] B)) (a : A) :
    commutativeHopfPointsMap f p a = f (p a) := rfl

/-- Coefficient automorphisms induce actual automorphisms of the point group. -/
def commutativeHopfPointsAutomorphism (e : B ≃ₐ[R] B) :
    WithConv (A →ₐ[R] B) ≃* WithConv (A →ₐ[R] B) where
  toFun p := toConv (e.toAlgHom.comp p.ofConv)
  invFun p := toConv (e.symm.toAlgHom.comp p.ofConv)
  left_inv p := by
    apply WithConv.ext
    ext a
    exact e.symm_apply_apply (p a)
  right_inv p := by
    apply WithConv.ext
    ext a
    exact e.apply_symm_apply (p a)
  map_mul' p q := (commutativeHopfPointsMap e.toAlgHom).map_mul p q

/-- Evaluation of the induced automorphism is the original coefficient automorphism acting on the original point. -/
theorem commutativeHopfPointsAutomorphism_apply (e : B ≃ₐ[R] B)
    (p : WithConv (A →ₐ[R] B)) (a : A) :
    commutativeHopfPointsAutomorphism e p a = e (p a) := rfl

/-- The original coefficient-automorphism group acts on the actual group of points by group automorphisms. -/
def commutativeHopfPointsCoefficientAction :
    (B ≃ₐ[R] B) →* MulAut (WithConv (A →ₐ[R] B)) where
  toFun := commutativeHopfPointsAutomorphism
  map_one' := by
    ext p a
    rfl
  map_mul' e f := by
    ext p a
    rfl

/-- This action applies the same coefficient automorphism to each genuine coordinate value. -/
theorem commutativeHopfPointsCoefficientAction_apply (e : B ≃ₐ[R] B)
    (p : WithConv (A →ₐ[R] B)) (a : A) :
    commutativeHopfPointsCoefficientAction e p a = e (p a) := by
  rfl

end
end Dubon2026
