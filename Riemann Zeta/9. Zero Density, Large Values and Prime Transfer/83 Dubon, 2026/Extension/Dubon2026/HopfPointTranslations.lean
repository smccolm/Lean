import Dubon2026.CommutativeHopfPointsCoefficientChange

/-! # Actual translations on original Hopf coordinates -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The original point group, with its already constructed antipode inverse. -/
local instance hopfTranslationPointGroup : Group (WithConv (A →ₐ[R] R)) :=
  commutativeHopfPointsGroup

/-- Translation by a genuine original point acts on coordinates by convolution of the universal original point with the scalar-extended given point. -/
def hopfPointTranslation (p : WithConv (A →ₐ[R] R)) : A →ₐ[R] A :=
  (toConv (AlgHom.id R A) * commutativeHopfPointsMap (Algebra.ofId R A) p).ofConv

/-- The original identity point gives the identity coordinate translation. -/
theorem hopfPointTranslation_one :
    hopfPointTranslation (1 : WithConv (A →ₐ[R] R)) = AlgHom.id R A := by
  simp [hopfPointTranslation]

/-- Composition of the actual coordinate translations follows the original convolution product. -/
theorem hopfPointTranslation_comp (p q : WithConv (A →ₐ[R] R)) :
    (hopfPointTranslation p).comp (hopfPointTranslation q) = hopfPointTranslation (p * q) := by
  let c := commutativeHopfPointsMap (A := A) (Algebra.ofId R A)
  have hs : (hopfPointTranslation p).comp (c q).ofConv = (c q).ofConv := by
    apply AlgHom.ext
    intro a
    exact (hopfPointTranslation p).commutes (q a)
  calc
    _ = (toConv (hopfPointTranslation p) *
        toConv ((hopfPointTranslation p).comp (c q).ofConv)).ofConv := by
      simpa only [AlgHom.comp_id] using AlgHom.comp_convMul_distrib
        (hopfPointTranslation p) (toConv (AlgHom.id R A)) (c q)
    _ = ((toConv (AlgHom.id R A) * c p) * c q).ofConv := by rw [hs]; rfl
    _ = (toConv (AlgHom.id R A) * (c p * c q)).ofConv := by rw [mul_assoc]
    _ = _ := by rw [← c.map_mul]; rfl

/-- The original antipode inverse point gives the inverse of the actual coordinate translation. -/
def hopfPointTranslationEquiv (p : WithConv (A →ₐ[R] R)) : A ≃ₐ[R] A :=
  { hopfPointTranslation p with
    invFun := hopfPointTranslation p⁻¹
    left_inv := fun a => by
      have h := AlgHom.congr_fun (hopfPointTranslation_comp p⁻¹ p) a
      simpa only [inv_mul_cancel, hopfPointTranslation_one, AlgHom.id_apply] using h
    right_inv := fun a => by
      have h := AlgHom.congr_fun (hopfPointTranslation_comp p p⁻¹) a
      simpa only [mul_inv_cancel, hopfPointTranslation_one, AlgHom.id_apply] using h }

/-- The genuine original point group acts on the actual coordinate algebra by algebra automorphisms. -/
def hopfPointTranslationAction : WithConv (A →ₐ[R] R) →* (A ≃ₐ[R] A) where
  toFun := hopfPointTranslationEquiv
  map_one' := AlgEquiv.coe_algHom_injective hopfPointTranslation_one
  map_mul' p q := AlgEquiv.coe_algHom_injective (hopfPointTranslation_comp p q).symm

/-- Evaluating an actual translated coordinate at an original point gives the original product point, fixing the geometric meaning of the action. -/
theorem hopfPointTranslation_evaluation (p q : WithConv (A →ₐ[R] R)) (a : A) :
    p (hopfPointTranslation q a) = (p * q) a := by
  let c := commutativeHopfPointsMap (A := A) (Algebra.ofId R A)
  have hs : p.ofConv.comp (c q).ofConv = q.ofConv := by
    apply AlgHom.ext
    intro b
    exact p.ofConv.commutes (q b)
  have h := AlgHom.congr_fun (AlgHom.comp_convMul_distrib p.ofConv
    (toConv (AlgHom.id R A)) (c q)) a
  simpa only [AlgHom.comp_id, hs, toConv_ofConv] using h

end
end Dubon2026
