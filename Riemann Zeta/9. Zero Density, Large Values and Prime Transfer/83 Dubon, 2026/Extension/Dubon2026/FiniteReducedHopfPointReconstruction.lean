import Dubon2026.FiniteReducedPointEvaluation
import Dubon2026.FiniteReducedTensorPointSeparation
import Dubon2026.HopfAntipodeCoordinateDiagrams
import Mathlib.RingTheory.Bialgebra.Equiv

/-! # Genuine Hopf coordinates reconstructed from their actual geometric point groups -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {K A B : Type*} [Field K] [IsAlgClosed K]
  [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [IsReduced A]
  [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [IsReduced B]

/-- The original source point group in the genuine coordinate reconstruction. -/
local instance reducedHopfSourcePoints : Group (WithConv (A →ₐ[K] K)) :=
  commutativeHopfPointsGroup

/-- The original target point group in the genuine coordinate reconstruction. -/
local instance reducedHopfTargetPoints : Group (WithConv (B →ₐ[K] K)) :=
  commutativeHopfPointsGroup

private def originalPointEquiv
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K)) :
    (A →ₐ[K] K) ≃ (B →ₐ[K] K) where
  toFun p := (e (toConv p)).ofConv
  invFun q := (e.symm (toConv q)).ofConv
  left_inv p := congrArg WithConv.ofConv (e.symm_apply_apply (toConv p))
  right_inv q := congrArg WithConv.ofConv (e.apply_symm_apply (toConv q))

/-- The actual finite reduced coordinate algebra equivalence induced contravariantly by the given equivalence of genuine geometric point groups. Both coordinate reconstructions use proved original evaluation bijectivity. -/
def finiteReducedHopfPointCoordinateEquiv
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K)) : B ≃ₐ[K] A :=
  (finiteReducedPointEvaluationEquiv (K := K) (A := B)).trans
    ((AlgEquiv.piCongrLeft' K (fun _ : B →ₐ[K] K => K) (originalPointEquiv e).symm).trans
      (finiteReducedPointEvaluationEquiv (K := K) (A := A)).symm)

/-- Evaluation of the reconstructed original coordinate is evaluation of the original point's image. -/
theorem finiteReducedHopfPointCoordinateEquiv_eval
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K))
    (b : B) (p : WithConv (A →ₐ[K] K)) :
    p (finiteReducedHopfPointCoordinateEquiv e b) = e p b := by
  exact congrFun ((finiteReducedPointEvaluationEquiv (K := K) (A := A)).apply_symm_apply
    ((AlgEquiv.piCongrLeft' K (fun _ : B →ₐ[K] K => K) (originalPointEquiv e).symm)
      (finiteReducedPointEvaluationEquiv b))) p.ofConv

/-- The genuine point identity determines the original counit of the reconstructed coordinate equivalence. -/
theorem finiteReducedHopfPointCoordinateEquiv_counit
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K)) :
    (Bialgebra.counitAlgHom K A).comp (finiteReducedHopfPointCoordinateEquiv e).toAlgHom =
      Bialgebra.counitAlgHom K B := by
  apply AlgHom.ext
  intro b
  have h := finiteReducedHopfPointCoordinateEquiv_eval e b 1
  rw [map_one] at h
  exact h

omit [IsAlgClosed K] in
/-- Original convolution of genuine points is evaluation of the same original comultiplication. -/
private theorem originalPointProduct_comul
    {C : Type*} [CommRing C] [HopfAlgebra K C]
    (p q : WithConv (C →ₐ[K] K)) (c : C) :
    Algebra.TensorProduct.productMap p.ofConv q.ofConv (Coalgebra.comul c) = (p * q) c := by
  rw [AlgHom.convMul_apply]
  have h : Algebra.TensorProduct.productMap p.ofConv q.ofConv =
      Algebra.TensorProduct.lift p.ofConv q.ofConv (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rfl
  exact AlgHom.congr_fun h _

/-- Genuine multiplication of all original point pairs determines the exact original comultiplication diagram, using proved separation of the original reduced tensor algebra. -/
theorem finiteReducedHopfPointCoordinateEquiv_comul
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K)) :
    (Algebra.TensorProduct.map (finiteReducedHopfPointCoordinateEquiv e).toAlgHom
      (finiteReducedHopfPointCoordinateEquiv e).toAlgHom).comp (Bialgebra.comulAlgHom K B) =
      (Bialgebra.comulAlgHom K A).comp (finiteReducedHopfPointCoordinateEquiv e).toAlgHom := by
  let f := (finiteReducedHopfPointCoordinateEquiv e).toAlgHom
  apply AlgHom.ext
  intro b
  apply sub_eq_zero.mp
  apply finiteReducedTensor_eq_zero_of_point_pairs (F := K) (K := K)
  intro p q
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hmap : (Algebra.TensorProduct.productMap p q).comp (Algebra.TensorProduct.map f f) =
      Algebra.TensorProduct.productMap (e (toConv p)).ofConv (e (toConv q)).ofConv := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change p (f x) * q (f y) = e (toConv p) x * e (toConv q) y
    exact congrArg₂ (fun a b : K => a * b)
      (finiteReducedHopfPointCoordinateEquiv_eval e x (toConv p))
      (finiteReducedHopfPointCoordinateEquiv_eval e y (toConv q))
  calc
    _ = Algebra.TensorProduct.productMap (e (toConv p)).ofConv (e (toConv q)).ofConv
        (Coalgebra.comul b) := AlgHom.congr_fun hmap _
    _ = (e (toConv p) * e (toConv q)) b := originalPointProduct_comul _ _ _
    _ = e (toConv p * toConv q) b := congrArg (fun r : WithConv (B →ₐ[K] K) => r b)
      (e.map_mul _ _).symm
    _ = (toConv p * toConv q) (f b) :=
      (finiteReducedHopfPointCoordinateEquiv_eval e b _).symm
    _ = _ := (originalPointProduct_comul (toConv p) (toConv q) (f b)).symm

/-- Construct the genuine equivalence of the original finite reduced Hopf coordinate bialgebras, retaining the actual reconstructed algebra maps and both original coalgebra diagrams. -/
def finiteReducedHopfPointBialgEquiv
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K)) : B ≃ₐc[K] A :=
  BialgEquiv.ofAlgEquiv (finiteReducedHopfPointCoordinateEquiv e)
    (finiteReducedHopfPointCoordinateEquiv_counit e)
    (finiteReducedHopfPointCoordinateEquiv_comul e)

/-- The reconstructed genuine coordinate equivalence commutes with the original antipodes, by its actual bialgebra structure. -/
theorem finiteReducedHopfPointBialgEquiv_antipode
    (e : WithConv (A →ₐ[K] K) ≃* WithConv (B →ₐ[K] K)) (b : B) :
    finiteReducedHopfPointBialgEquiv e (HopfAlgebra.antipode K b) =
      HopfAlgebra.antipode K (finiteReducedHopfPointBialgEquiv e b) := by
  exact hopfCoordinateMap_antipode (finiteReducedHopfPointBialgEquiv e).toBialgHom b

end
end Dubon2026
