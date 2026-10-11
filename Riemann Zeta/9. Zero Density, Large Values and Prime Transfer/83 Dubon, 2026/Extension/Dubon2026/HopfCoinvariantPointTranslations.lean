import Dubon2026.HopfSubgroupCoinvariants
import Dubon2026.HopfPointTranslations
import Dubon2026.TensorPointFamilySeparation

/-! # The original subgroup coaction and actual point translations -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {K A B ι : Type*} [CommRing K] [CommRing A] [HopfAlgebra K A]
  [CommRing B] [Bialgebra K B]

/-- Evaluating the actual subgroup factor in the original coaction gives precisely translation by the original restricted subgroup point. -/
theorem hopfCoinvariant_point_translation (q : A →ₐc[K] B) (p : B →ₐ[K] K) (a : A) :
    Algebra.TensorProduct.productMap (AlgHom.id K A) ((Algebra.ofId K A).comp p)
      (hopfSubgroupRightCoaction q a) =
      hopfPointTranslation (toConv (p.comp q.toAlgHom)) a := by
  have h : (Algebra.TensorProduct.productMap (AlgHom.id K A) ((Algebra.ofId K A).comp p)).comp
      (Algebra.TensorProduct.map (AlgHom.id K A) q.toAlgHom) =
      Algebra.TensorProduct.productMap (AlgHom.id K A)
        ((Algebra.ofId K A).comp (p.comp q.toAlgHom)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rfl
  change ((Algebra.TensorProduct.productMap (AlgHom.id K A)
    ((Algebra.ofId K A).comp p)).comp
      (Algebra.TensorProduct.map (AlgHom.id K A) q.toAlgHom)) (Coalgebra.comul a) = _
  rw [h]
  exact (AlgHom.convMul_apply (toConv (AlgHom.id K A))
    (commutativeHopfPointsMap (Algebra.ofId K A) (toConv (p.comp q.toAlgHom))) a).symm

/-- Partial point evaluation is the actual right tensor map followed by the original scalar-unit equivalence. -/
private theorem hopfTensorRightPoint_linear (p : B →ₐ[K] K) (z : A ⊗[K] B) :
    Algebra.TensorProduct.productMap (AlgHom.id K A) ((Algebra.ofId K A).comp p) z =
      TensorProduct.rid K A (p.toLinearMap.lTensor A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    change a * algebraMap K A (p b) = p b • a
    rw [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If a genuine finite family of subgroup points separates its original coordinate algebra, literal coaction invariance is equivalent to invariance under the actual original point translations. Tensor separation is derived from flatness rather than assumed. -/
theorem hopfCoinvariant_iff_pointTranslations [Module.Flat K A] [Finite ι]
    (q : A →ₐc[K] B) (p : ι → B →ₐ[K] K)
    (hp : Function.Injective (fun b : B => fun i : ι => p i b)) (a : A) :
    a ∈ hopfSubgroupCoinvariants q ↔
      ∀ i : ι, hopfPointTranslation (toConv ((p i).comp q.toAlgHom)) a = a := by
  change hopfSubgroupRightCoaction q a = a ⊗ₜ[K] (1 : B) ↔ _
  constructor
  · intro ha i
    rw [← hopfCoinvariant_point_translation q (p i) a, ha]
    simp
  · intro ha
    apply tensorPointFamily_separates p hp
    funext i
    apply (TensorProduct.rid K A).injective
    rw [← hopfTensorRightPoint_linear, ← hopfTensorRightPoint_linear,
      hopfCoinvariant_point_translation, ha i]
    simp

end
end Dubon2026
