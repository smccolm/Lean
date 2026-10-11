import Dubon2026.GaloisHopfOriginalCoordinateHom

/-! # Genuine original-field algebra equivalence determined by Galois-equivariant geometric points -/

namespace Dubon2026
noncomputable section
open WithConv

variable {F K A B : Type*} [Field F] [PerfectField F]
  [Field K] [Algebra F K] [IsAlgClosed K] [IsGalois F K]
  [CommRing A] [HopfAlgebra F A] [Module.Finite F A] [IsReduced A]
  [CommRing B] [HopfAlgebra F B] [Module.Finite F B] [IsReduced B]

/-- The original source point group in the original-field algebra equivalence. -/
local instance originalCoordinateEquivSourcePoints : Group (WithConv (A →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- The original target point group in the original-field algebra equivalence. -/
local instance originalCoordinateEquivTargetPoints : Group (WithConv (B →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- Descend both directions of the original Galois-equivariant point-group equivalence. Their exact original point evaluation and genuine point separation prove inverse original coordinate maps, constructing an algebra equivalence over the original field. -/
def galoisHopfOriginalCoordinateEquiv
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p)) :
    B ≃ₐ[F] A := by
  have hi : ∀ (g : K ≃ₐ[F] K) (p : WithConv (B →ₐ[F] K)),
      e.symm (commutativeHopfPointsAutomorphism g p) =
        commutativeHopfPointsAutomorphism g (e.symm p) := by
    intro g p
    apply e.injective
    rw [MulEquiv.apply_symm_apply, he, MulEquiv.apply_symm_apply]
  let f := galoisHopfOriginalCoordinateHom e he
  let r := galoisHopfOriginalCoordinateHom e.symm hi
  apply AlgEquiv.ofAlgHom f r
  · apply AlgHom.ext
    intro a
    apply sub_eq_zero.mp
    apply finiteReducedAlgebra_eq_zero_of_points (F := F) (K := K)
    intro p
    rw [map_sub]
    apply sub_eq_zero.mpr
    calc
      _ = e (toConv p) (r a) := galoisHopfOriginalCoordinateHom_eval e he (r a) (toConv p)
      _ = e.symm (e (toConv p)) a := galoisHopfOriginalCoordinateHom_eval e.symm hi a _
      _ = p a := by rw [MulEquiv.symm_apply_apply]
  · apply AlgHom.ext
    intro b
    apply sub_eq_zero.mp
    apply finiteReducedAlgebra_eq_zero_of_points (F := F) (K := K)
    intro p
    rw [map_sub]
    apply sub_eq_zero.mpr
    calc
      _ = e.symm (toConv p) (f b) := galoisHopfOriginalCoordinateHom_eval e.symm hi (f b) (toConv p)
      _ = e (e.symm (toConv p)) b := galoisHopfOriginalCoordinateHom_eval e he b _
      _ = p b := by rw [MulEquiv.apply_symm_apply]

/-- The genuine original-field algebra equivalence realizes exactly the original geometric point-group equivalence on every original coordinate. -/
theorem galoisHopfOriginalCoordinateEquiv_eval
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p))
    (b : B) (p : WithConv (A →ₐ[F] K)) :
    p (galoisHopfOriginalCoordinateEquiv e he b) = e p b := by
  exact galoisHopfOriginalCoordinateHom_eval e he b p

end
end Dubon2026
