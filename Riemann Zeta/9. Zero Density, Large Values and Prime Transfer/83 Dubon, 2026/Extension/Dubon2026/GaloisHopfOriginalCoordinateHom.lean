import Dubon2026.GaloisHopfCoordinateImage

/-! # Genuine original-field coordinate homomorphism recovered from Galois-equivariant points -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {F K A B : Type*} [Field F] [PerfectField F]
  [Field K] [Algebra F K] [IsAlgClosed K] [IsGalois F K]
  [CommRing A] [HopfAlgebra F A] [Module.Finite F A] [IsReduced A]
  [CommRing B] [HopfAlgebra F B] [Module.Finite F B] [IsReduced B]

/-- The original source point group for original-field coordinate descent. -/
local instance originalCoordinateHomSourcePoints : Group (WithConv (A →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- The original target point group for original-field coordinate descent. -/
local instance originalCoordinateHomTargetPoints : Group (WithConv (B →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- The original-field algebra homomorphism obtained by restricting the genuine reconstructed geometric map to the proved image of the actual original coordinate inclusion. -/
def galoisHopfOriginalCoordinateHom
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p)) :
    B →ₐ[F] A := by
  let i : A →ₐ[F] K ⊗[F] A := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Module.Flat.tensorProduct_mk_injective (R := F) (S := K) (M := A)
  let j : B →ₐ[F] K ⊗[F] A :=
    ((galoisHopfGeometricCoordinateEquiv e).toAlgHom.restrictScalars F).comp
      Algebra.TensorProduct.includeRight
  have hj (b : B) : j b ∈ i.range := galoisHopfGeometricCoordinateEquiv_original_image e he b
  exact (AlgEquiv.ofInjective i hi).symm.toAlgHom.comp (j.codRestrict i.range hj)

/-- The descended original coordinate has exactly the same scalar extension as the genuine reconstructed geometric coordinate, on every original input. -/
theorem galoisHopfOriginalCoordinateHom_scalarExtension
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p))
    (b : B) :
    (1 : K) ⊗ₜ[F] galoisHopfOriginalCoordinateHom e he b =
      galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b) := by
  let i : A →ₐ[F] K ⊗[F] A := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Module.Flat.tensorProduct_mk_injective (R := F) (S := K) (M := A)
  let j : B →ₐ[F] K ⊗[F] A :=
    ((galoisHopfGeometricCoordinateEquiv e).toAlgHom.restrictScalars F).comp
      Algebra.TensorProduct.includeRight
  let x : i.range := ⟨j b, galoisHopfGeometricCoordinateEquiv_original_image e he b⟩
  exact congrArg Subtype.val ((AlgEquiv.ofInjective i hi).apply_symm_apply x)

/-- Evaluation of the genuine descended original coordinate realizes the original Galois-equivariant point-group equivalence on every original point. -/
theorem galoisHopfOriginalCoordinateHom_eval
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p))
    (b : B) (p : WithConv (A →ₐ[F] K)) :
    p (galoisHopfOriginalCoordinateHom e he b) = e p b := by
  calc
    _ = AlgHom.liftEquiv F K A K p.ofConv
        ((1 : K) ⊗ₜ[F] galoisHopfOriginalCoordinateHom e he b) :=
      (algebraBaseChangePoint_original p.ofConv _).symm
    _ = AlgHom.liftEquiv F K A K p.ofConv
        (galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b)) :=
      congrArg (AlgHom.liftEquiv F K A K p.ofConv)
        (galoisHopfOriginalCoordinateHom_scalarExtension e he b)
    _ = _ := galoisHopfGeometricCoordinateEquiv_original_eval e b p.ofConv

end
end Dubon2026
