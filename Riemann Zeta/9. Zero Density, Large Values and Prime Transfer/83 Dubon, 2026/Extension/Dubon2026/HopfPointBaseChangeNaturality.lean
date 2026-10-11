import Dubon2026.HopfBaseChangePoints
import Dubon2026.HopfPointsRestriction
import Dubon2026.HopfCoinvariantBaseChange

/-! # Original point restriction commutes with genuine scalar extension -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R S A B K : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [HopfAlgebra R A] [CommRing B] [HopfAlgebra R B]
  [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

/-- The genuine point-group scalar extension intertwines restriction along the same original bialgebra map with restriction along its actual scalar extension. -/
theorem hopfBaseChangePointsEquiv_restriction (q : A →ₐc[R] B)
    (p : WithConv (B →ₐ[R] K)) :
    hopfBaseChangePointsEquiv (F := S) (hopfPointsRestriction q p) =
      hopfPointsRestriction (hopfBaseChangeCoordinateMap (S := S) q)
        (hopfBaseChangePointsEquiv (F := S) p) := by
  apply WithConv.ext
  apply (AlgHom.liftEquiv R S A K).symm.injective
  ext a
  simp only [AlgHom.liftEquiv_symm_apply]
  change (AlgHom.liftEquiv R S A K (p.ofConv.comp q.toAlgHom)) (1 ⊗ₜ[R] a) =
    (AlgHom.liftEquiv R S B K p.ofConv)
      ((Algebra.TensorProduct.map (AlgHom.id S S) q.toAlgHom) (1 ⊗ₜ[R] a))
  rw [Algebra.TensorProduct.map_tmul]
  simp only [AlgHom.id_apply, algebraBaseChangePoint_original, AlgHom.comp_apply]

/-- Restricting the actual scalar-extended point to the original coordinates commutes with the original subgroup point restriction. -/
theorem hopfBaseChangePointsEquiv_symm_restriction (q : A →ₐc[R] B)
    (p : WithConv (S ⊗[R] B →ₐ[S] K)) :
    (hopfBaseChangePointsEquiv (R := R) (F := S) (A := A) (K := K)).symm
        (hopfPointsRestriction (hopfBaseChangeCoordinateMap (S := S) q) p) =
      hopfPointsRestriction q ((hopfBaseChangePointsEquiv (F := S)).symm p) := by
  apply (hopfBaseChangePointsEquiv (R := R) (F := S) (A := A) (K := K)).injective
  rw [MulEquiv.apply_symm_apply, hopfBaseChangePointsEquiv_restriction,
    MulEquiv.apply_symm_apply]

end
end Dubon2026
