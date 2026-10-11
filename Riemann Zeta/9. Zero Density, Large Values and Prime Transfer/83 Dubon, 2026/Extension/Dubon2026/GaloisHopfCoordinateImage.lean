import Dubon2026.FiniteReducedHopfPointReconstruction
import Dubon2026.FiniteReducedScalarExtension
import Dubon2026.HopfBaseChangePoints
import Dubon2026.GaloisTensorPointEvaluation

/-! # Original coordinate images under the geometric reconstruction of a genuine Galois point equivalence -/

namespace Dubon2026
noncomputable section
open WithConv Module
open scoped TensorProduct

variable {F K A B : Type*} [Field F] [PerfectField F]
  [Field K] [Algebra F K] [IsAlgClosed K]
  [CommRing A] [HopfAlgebra F A] [Module.Finite F A] [IsReduced A]
  [CommRing B] [HopfAlgebra F B] [Module.Finite F B] [IsReduced B]

/-- The genuine original source point group in the Galois coordinate comparison. -/
local instance galoisCoordinateSourcePoints : Group (WithConv (A →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- The genuine original target point group in the Galois coordinate comparison. -/
local instance galoisCoordinateTargetPoints : Group (WithConv (B →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- Reconstruct the actual geometric coordinate algebra equivalence from the original point-group equivalence and the genuine original point base-change equivalences. -/
def galoisHopfGeometricCoordinateEquiv
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K)) :
    K ⊗[F] B ≃ₐ[K] K ⊗[F] A := by
  letI := finiteReducedAlgebra_scalarExtension_isReduced (F := F) (K := K) (A := A)
  letI := finiteReducedAlgebra_scalarExtension_isReduced (F := F) (K := K) (A := B)
  exact finiteReducedHopfPointCoordinateEquiv
    (((hopfBaseChangePointsEquiv (R := F) (F := K) (A := A) (K := K)).symm.trans e).trans
      (hopfBaseChangePointsEquiv (R := F) (F := K) (A := B) (K := K)))

/-- The reconstructed geometric coordinate of an original element evaluates at the same original point through the original point-group equivalence. -/
theorem galoisHopfGeometricCoordinateEquiv_original_eval
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K)) (b : B) (p : A →ₐ[F] K) :
    AlgHom.liftEquiv F K A K p
      (galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b)) = e (toConv p) b := by
  letI := finiteReducedAlgebra_scalarExtension_isReduced (F := F) (K := K) (A := A)
  letI := finiteReducedAlgebra_scalarExtension_isReduced (F := F) (K := K) (A := B)
  let ea := hopfBaseChangePointsEquiv (R := F) (F := K) (A := A) (K := K)
  let eb := hopfBaseChangePointsEquiv (R := F) (F := K) (A := B) (K := K)
  let ek := (ea.symm.trans e).trans eb
  calc
    _ = ek (ea (toConv p)) ((1 : K) ⊗ₜ[F] b) :=
      finiteReducedHopfPointCoordinateEquiv_eval ek _ (ea (toConv p))
    _ = eb (e (toConv p)) ((1 : K) ⊗ₜ[F] b) := by
      dsimp only [ek, MulEquiv.trans_apply]
      rw [MulEquiv.symm_apply_apply]
    _ = _ := algebraBaseChangePoint_original (e (toConv p)).ofConv b

/-- Genuine Galois equivariance of the original point-group equivalence forces the reconstructed image of every original coordinate to be fixed under actual semilinear coefficient action. -/
theorem galoisHopfGeometricCoordinateEquiv_original_fixed
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p))
    (b : B) (g : K ≃ₐ[F] K) :
    galoisTensorCoefficientAutomorphism g
      (galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b)) =
        galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b) := by
  letI := finiteReducedAlgebra_scalarExtension_isReduced (F := F) (K := K) (A := A)
  let z := galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b)
  apply sub_eq_zero.mp
  apply finiteReducedAlgebra_eq_zero_of_points (F := K) (K := K)
  intro r
  rw [map_sub]
  apply sub_eq_zero.mpr
  let p := (AlgHom.liftEquiv F K A K).symm r
  have hp : AlgHom.liftEquiv F K A K p = r := (AlgHom.liftEquiv F K A K).apply_symm_apply r
  have heval : e (toConv (g.symm.toAlgHom.comp p)) b = g.symm (e (toConv p) b) :=
    congrArg (fun t : WithConv (B →ₐ[F] K) => t b) (he g.symm (toConv p))
  calc
    _ = g (AlgHom.liftEquiv F K A K (g.symm.toAlgHom.comp p) z) := by
      rw [← hp]
      exact galoisTensorCoefficientAutomorphism_point g p z
    _ = g (e (toConv (g.symm.toAlgHom.comp p)) b) :=
      congrArg g (galoisHopfGeometricCoordinateEquiv_original_eval e b _)
    _ = e (toConv p) b := by rw [heval, AlgEquiv.apply_symm_apply]
    _ = r z := by
      rw [← hp]
      exact (galoisHopfGeometricCoordinateEquiv_original_eval e b p).symm

/-- Over the original Galois extension, the actual reconstructed image of each original coordinate is the scalar extension of an original coordinate. The same finite original basis and proved Galois tensor descent produce that coordinate. -/
theorem galoisHopfGeometricCoordinateEquiv_original_image [IsGalois F K]
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p))
    (b : B) :
    ∃ a : A, (1 : K) ⊗ₜ[F] a = galoisHopfGeometricCoordinateEquiv e ((1 : K) ⊗ₜ[F] b) := by
  apply (galoisTensorCoefficientAutomorphism_fixed_iff (Module.Free.chooseBasis F A) _).mp
  exact galoisHopfGeometricCoordinateEquiv_original_fixed e he b

end
end Dubon2026
