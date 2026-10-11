import Dubon2026.GaloisHopfOriginalCoordinateEquiv

/-! # Genuine original Hopf coordinate equivalence from actual Galois-equivariant point groups -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {F K A B : Type*} [Field F] [PerfectField F]
  [Field K] [Algebra F K] [IsAlgClosed K] [IsGalois F K]
  [CommRing A] [HopfAlgebra F A] [Module.Finite F A] [IsReduced A]
  [CommRing B] [HopfAlgebra F B] [Module.Finite F B] [IsReduced B]

/-- The original source point group for the genuine Hopf coordinate descent. -/
local instance originalBialgEquivSourcePoints : Group (WithConv (A →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- The original target point group for the genuine Hopf coordinate descent. -/
local instance originalBialgEquivTargetPoints : Group (WithConv (B →ₐ[F] K)) :=
  commutativeHopfPointsGroup

omit [PerfectField F] [IsAlgClosed K] [IsGalois F K] in
/-- Evaluation of the original tensor product map is precisely the original convolution product. -/
private theorem originalFieldPointProduct_comul
    {C : Type*} [CommRing C] [HopfAlgebra F C]
    (p q : WithConv (C →ₐ[F] K)) (c : C) :
    Algebra.TensorProduct.productMap p.ofConv q.ofConv (Coalgebra.comul c) = (p * q) c := by
  rw [Algebra.TensorProduct.productMap_eq_comp_map]
  rfl

/-- The original descended coordinate equivalence preserves the actual original counit, by the original point identity and faithfulness of the point field. -/
theorem galoisHopfOriginalCoordinateEquiv_counit
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p)) :
    (Bialgebra.counitAlgHom F A).comp (galoisHopfOriginalCoordinateEquiv e he).toAlgHom =
      Bialgebra.counitAlgHom F B := by
  apply AlgHom.ext
  intro b
  apply (algebraMap F K).injective
  have h := galoisHopfOriginalCoordinateEquiv_eval e he b 1
  rw [map_one] at h
  exact h

/-- Genuine multiplication in the original point groups determines the exact original-field comultiplication diagram through proved separation of the original reduced tensor coordinates. -/
theorem galoisHopfOriginalCoordinateEquiv_comul
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p)) :
    (Algebra.TensorProduct.map (galoisHopfOriginalCoordinateEquiv e he).toAlgHom
      (galoisHopfOriginalCoordinateEquiv e he).toAlgHom).comp (Bialgebra.comulAlgHom F B) =
      (Bialgebra.comulAlgHom F A).comp (galoisHopfOriginalCoordinateEquiv e he).toAlgHom := by
  let f := (galoisHopfOriginalCoordinateEquiv e he).toAlgHom
  apply AlgHom.ext
  intro b
  apply sub_eq_zero.mp
  apply finiteReducedTensor_eq_zero_of_point_pairs (F := F) (K := K)
  intro p q
  rw [map_sub]
  apply sub_eq_zero.mpr
  have ht : (Algebra.TensorProduct.productMap p q).comp (Algebra.TensorProduct.map f f) =
      Algebra.TensorProduct.productMap (e (toConv p)).ofConv (e (toConv q)).ofConv := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change p (f x) * q (f y) = e (toConv p) x * e (toConv q) y
    exact congrArg₂ (fun a b : K => a * b)
      (galoisHopfOriginalCoordinateEquiv_eval e he x (toConv p))
      (galoisHopfOriginalCoordinateEquiv_eval e he y (toConv q))
  calc
    _ = Algebra.TensorProduct.productMap (e (toConv p)).ofConv (e (toConv q)).ofConv
        (Coalgebra.comul b) := AlgHom.congr_fun ht _
    _ = (e (toConv p) * e (toConv q)) b :=
      originalFieldPointProduct_comul _ _ _
    _ = e (toConv p * toConv q) b :=
      congrArg (fun r : WithConv (B →ₐ[F] K) => r b) (e.map_mul _ _).symm
    _ = (toConv p * toConv q) (f b) :=
      (galoisHopfOriginalCoordinateEquiv_eval e he b _).symm
    _ = _ := (originalFieldPointProduct_comul (toConv p) (toConv q) (f b)).symm

/-- The original finite reduced Hopf coordinate algebras are genuinely equivalent over the original field when their actual geometric point groups are Galois-equivariantly equivalent. Both original algebra maps and coalgebra diagrams have been constructed and proved. -/
def galoisHopfOriginalBialgEquiv
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p)) :
    B ≃ₐc[F] A :=
  BialgEquiv.ofAlgEquiv (galoisHopfOriginalCoordinateEquiv e he)
    (galoisHopfOriginalCoordinateEquiv_counit e he)
    (galoisHopfOriginalCoordinateEquiv_comul e he)

/-- The genuine reconstructed original-field bialgebra equivalence preserves the original Hopf antipodes. -/
theorem galoisHopfOriginalBialgEquiv_antipode
    (e : WithConv (A →ₐ[F] K) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)),
      e (commutativeHopfPointsAutomorphism g p) = commutativeHopfPointsAutomorphism g (e p))
    (b : B) :
    galoisHopfOriginalBialgEquiv e he (HopfAlgebra.antipode F b) =
      HopfAlgebra.antipode F (galoisHopfOriginalBialgEquiv e he b) := by
  exact hopfCoordinateMap_antipode (galoisHopfOriginalBialgEquiv e he).toBialgHom b

end
end Dubon2026
