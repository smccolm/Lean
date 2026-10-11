import Dubon2026.HopfPointsRestriction
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Original antipode compatibility with coordinate maps and comultiplication -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [HopfAlgebra R B]

/-- A genuine coordinate bialgebra map commutes with the original antipodes, by preservation of inverses in the actual point groups. -/
theorem hopfCoordinateMap_antipode (q : A →ₐc[R] B) (a : A) :
    q (HopfAlgebra.antipode R a) = HopfAlgebra.antipode R (q a) := by
  letI : Group (WithConv (A →ₐ[R] B)) := commutativeHopfPointsGroup
  letI : Group (WithConv (B →ₐ[R] B)) := commutativeHopfPointsGroup
  exact (congrArg (fun p : WithConv (A →ₐ[R] B) => p a)
    ((hopfPointsRestriction q).map_inv (toConv (AlgHom.id R B)))).symm

/-- Multiplying the two actual coordinate inclusions evaluates the tensor map on original comultiplication. -/
private theorem tensorCoordinatePoint_product (f g : A →ₐ[R] A) :
    toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).comp f) *
      toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).comp g) =
      toConv ((Algebra.TensorProduct.map f g).comp (Bialgebra.comulAlgHom R A)) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  rw [AlgHom.convMul_apply]
  have h : Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).comp f)
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).comp g)
      (fun _ _ => Commute.all _ _) = Algebra.TensorProduct.map f g := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp
  exact AlgHom.congr_fun h (Coalgebra.comul a)

/-- For original cocommutative coordinates the actual antipode commutes with comultiplication, derived from inverses of the two universal coordinate points. -/
theorem hopfCocommutative_antipode_comul [Coalgebra.IsCocomm R A] (a : A) :
    Coalgebra.comul (HopfAlgebra.antipode R a) =
      (Algebra.TensorProduct.map (commutativeHopfAntipode (R := R))
        (commutativeHopfAntipode (R := R))) (Coalgebra.comul a) := by
  letI : Group (WithConv (A →ₐ[R] A ⊗[R] A)) := commutativeHopfPointsGroup
  let l : WithConv (A →ₐ[R] A ⊗[R] A) := toConv Algebra.TensorProduct.includeLeft
  let r : WithConv (A →ₐ[R] A ⊗[R] A) := toConv Algebra.TensorProduct.includeRight
  have hprod : l * r = toConv (Bialgebra.comulAlgHom R A) := by
    simpa only [AlgHom.comp_id, Algebra.TensorProduct.map_id, AlgHom.id_comp]
      using tensorCoordinatePoint_product (R := R) (AlgHom.id R A) (AlgHom.id R A)
  have hinv : (toConv (Bialgebra.comulAlgHom R A))⁻¹ = l⁻¹ * r⁻¹ := by
    rw [← hprod, mul_inv_rev, mul_comm]
  have h := congrArg (fun p : WithConv (A →ₐ[R] A ⊗[R] A) => p a) hinv
  change Coalgebra.comul (HopfAlgebra.antipode R a) =
    (toConv ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).comp
        (commutativeHopfAntipode (R := R))) *
      toConv ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).comp
        (commutativeHopfAntipode (R := R)))) a at h
  rw [tensorCoordinatePoint_product] at h
  exact h

end
end Dubon2026
