import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.Algebra.Group.MinimalAxioms

/-! # The actual convolution group of points of a commutative Hopf algebra -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A]
  [HopfAlgebra R A] [CommSemiring B] [Algebra R B]

/-- For a commutative coordinate algebra the actual antipode is an algebra homomorphism. -/
def commutativeHopfAntipode : A →ₐ[R] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one
    (fun a b => (HopfAlgebra.antipode_mul a b).trans (mul_comm _ _))

/-- Evaluation of this algebra homomorphism is exactly the original Hopf antipode. -/
theorem commutativeHopfAntipode_apply (a : A) :
    commutativeHopfAntipode (R := R) a = HopfAlgebra.antipode R a := rfl

/-- Composing a genuine algebra-valued point with the actual antipode gives its left convolution inverse. -/
theorem commutativeHopfPoints_inverse_mul (f : WithConv (A →ₐ[R] B)) :
    toConv (f.ofConv.comp (commutativeHopfAntipode (R := R))) * f = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  let s := Coalgebra.Repr.arbitrary R a
  calc
    (toConv (f.ofConv.comp (commutativeHopfAntipode (R := R))) * f) a =
        ∑ i ∈ s.index, f.ofConv (HopfAlgebra.antipode R (s.left i)) * f.ofConv (s.right i) := by
      change (toConv ((f.ofConv.comp (commutativeHopfAntipode (R := R))).toLinearMap) *
        toConv f.ofConv.toLinearMap) a = _
      exact s.convMul_apply _ _
    _ = f.ofConv (∑ i ∈ s.index, HopfAlgebra.antipode R (s.left i) * s.right i) := by
      simp only [map_sum, map_mul]
    _ = algebraMap R B (Coalgebra.counit a) := by
      rw [HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit s]
      exact f.ofConv.commutes _
    _ = (1 : WithConv (A →ₐ[R] B)) a := rfl

/-- The actual algebra-valued points form a group for the existing convolution multiplication. Its inverse is composition with the original antipode. -/
abbrev commutativeHopfPointsGroup : Group (WithConv (A →ₐ[R] B)) := by
  letI : Inv (WithConv (A →ₐ[R] B)) :=
    ⟨fun f => toConv (f.ofConv.comp (commutativeHopfAntipode (R := R)))⟩
  exact Group.ofLeftAxioms mul_assoc one_mul commutativeHopfPoints_inverse_mul

/-- In the constructed actual point group, inverse evaluation is composition with the original coordinate antipode. -/
theorem commutativeHopfPointsGroup_inv_apply (f : WithConv (A →ₐ[R] B)) (a : A) :
    letI := commutativeHopfPointsGroup (R := R) (A := A) (B := B)
    (f⁻¹) a = f (HopfAlgebra.antipode R a) := by
  rfl

end
end Dubon2026
