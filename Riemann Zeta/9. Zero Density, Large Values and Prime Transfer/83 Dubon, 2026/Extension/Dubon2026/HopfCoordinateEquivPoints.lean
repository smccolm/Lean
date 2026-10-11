import Dubon2026.HopfPointsRestriction
import Dubon2026.CommutativeHopfPointsCoefficientChange
import Mathlib.RingTheory.Bialgebra.Equiv

/-! # Genuine point-group and Galois transport through a coordinate equivalence -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B K : Type*} [CommRing R]
  [CommRing A] [HopfAlgebra R A] [CommRing B] [HopfAlgebra R B]
  [CommRing K] [Algebra R K]

/-- A genuine coordinate bialgebra equivalence gives the actual contravariant equivalence of the original convolution point groups. -/
def hopfCoordinateEquivPoints (e : B ≃ₐc[R] A) :
    WithConv (A →ₐ[R] K) ≃* WithConv (B →ₐ[R] K) where
  toFun := hopfPointsRestriction e.toBialgHom
  invFun := hopfPointsRestriction e.symm.toBialgHom
  left_inv p := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    change p (e (e.symm a)) = p a
    rw [e.apply_symm_apply]
  right_inv p := by
    apply WithConv.ext
    apply AlgHom.ext
    intro b
    change p (e.symm (e b)) = p b
    rw [e.symm_apply_apply]
  map_mul' := (hopfPointsRestriction e.toBialgHom).map_mul

/-- The actual point equivalence evaluates the original point on the same original coordinate image. -/
theorem hopfCoordinateEquivPoints_apply (e : B ≃ₐc[R] A)
    (p : WithConv (A →ₐ[R] K)) (b : B) :
    hopfCoordinateEquivPoints e p b = p (e b) := by
  rfl

/-- The actual coordinate point equivalence commutes with the original coefficient automorphisms. -/
theorem hopfCoordinateEquivPoints_coefficient (e : B ≃ₐc[R] A)
    (g : K ≃ₐ[R] K) (p : WithConv (A →ₐ[R] K)) :
    hopfCoordinateEquivPoints e (commutativeHopfPointsAutomorphism g p) =
      commutativeHopfPointsAutomorphism g (hopfCoordinateEquivPoints e p) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  rfl

end
end Dubon2026
