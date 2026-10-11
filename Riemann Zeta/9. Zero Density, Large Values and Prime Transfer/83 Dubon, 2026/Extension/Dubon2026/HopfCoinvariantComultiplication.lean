import Dubon2026.HopfSubgroupCoinvariants

/-! # Original comultiplication preserves one factor of invariant coordinates -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Bialgebra R B]

/-- Original coassociativity makes the comultiplication of an actual right-invariant coordinate invariant in its second factor. This derives the tensor-kernel condition from the original coaction identity. -/
theorem hopfCoinvariant_comul_right (q : A →ₐc[R] B) (a : A)
    (ha : a ∈ hopfSubgroupCoinvariants q) :
    (((hopfSubgroupRightCoaction q).toLinearMap -
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap).lTensor A)
        (Coalgebra.comul a) = 0 := by
  let d := Bialgebra.comulAlgHom R A
  let c := hopfSubgroupRightCoaction q
  let t := Algebra.TensorProduct.map (AlgHom.id R A)
    (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom)
  have hmap : Algebra.TensorProduct.map (AlgHom.id R A) c =
      t.comp (Algebra.TensorProduct.map (AlgHom.id R A) d) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rfl
  have hassoc : t.comp (Algebra.TensorProduct.assoc R R R A A A).toAlgHom =
      (Algebra.TensorProduct.assoc R R R A A B).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id R (A ⊗[R] A)) q.toAlgHom) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext_threefold
    intro x y z
    rfl
  have hswitch : (Algebra.TensorProduct.map (AlgHom.id R (A ⊗[R] A)) q.toAlgHom).comp
      (Algebra.TensorProduct.map d (AlgHom.id R A)) =
      (Algebra.TensorProduct.map d (AlgHom.id R B)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rfl
  have htail (z : A ⊗[R] A) :
      (Algebra.TensorProduct.assoc R R R A A B) (z ⊗ₜ[R] (1 : B)) =
        Algebra.TensorProduct.map (AlgHom.id R A)
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, hz, hw]
  have he : Algebra.TensorProduct.map (AlgHom.id R A) c (d a) =
      Algebra.TensorProduct.map (AlgHom.id R A)
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) (d a) := by
    calc
      _ = t ((Algebra.TensorProduct.map (AlgHom.id R A) d) (d a)) :=
        AlgHom.congr_fun hmap _
      _ = t ((Algebra.TensorProduct.assoc R R R A A A)
          ((Algebra.TensorProduct.map d (AlgHom.id R A)) (d a))) :=
        congrArg t (Coalgebra.coassoc_apply a).symm
      _ = (Algebra.TensorProduct.assoc R R R A A B)
          ((Algebra.TensorProduct.map (AlgHom.id R (A ⊗[R] A)) q.toAlgHom)
            ((Algebra.TensorProduct.map d (AlgHom.id R A)) (d a))) :=
        AlgHom.congr_fun hassoc _
      _ = (Algebra.TensorProduct.assoc R R R A A B)
          ((Algebra.TensorProduct.map d (AlgHom.id R B)) (c a)) :=
        congrArg (Algebra.TensorProduct.assoc R R R A A B) (AlgHom.congr_fun hswitch _)
      _ = (Algebra.TensorProduct.assoc R R R A A B) (d a ⊗ₜ[R] (1 : B)) := by
        rw [show c a = a ⊗ₜ[R] (1 : B) from ha]
        rfl
      _ = _ := htail (d a)
  change ((c.toLinearMap -
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap).lTensor A) (d a) = 0
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr he

end
end Dubon2026
