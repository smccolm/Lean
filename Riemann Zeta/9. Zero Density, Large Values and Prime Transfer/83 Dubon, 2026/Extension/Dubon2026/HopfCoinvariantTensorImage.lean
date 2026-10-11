import Dubon2026.HopfCoinvariantComultiplication
import Dubon2026.TensorKernelRetraction

/-! # Actual integral comultiplication takes values in invariant tensor coordinates -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [CommRing B] [Bialgebra R B] [Module.Free R B]

omit [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R A] [Module.Free R B] in
/-- A genuine linear retraction of the original invariant coordinates projects the original comultiplication into their tensor product without changing its image in the ambient coordinates. Coassociativity supplies one factor, cocommutativity the other, and flat-kernel exactness derives both tensor image conditions. -/
theorem hopfCoinvariant_tensor_image (q : A →ₐc[R] B)
    (p : A →ₗ[R] hopfSubgroupCoinvariants q)
    (hp : p.comp (hopfSubgroupCoinvariants q).val.toLinearMap = LinearMap.id)
    (a : hopfSubgroupCoinvariants q) :
    TensorProduct.map (hopfSubgroupCoinvariants q).val.toLinearMap
      (hopfSubgroupCoinvariants q).val.toLinearMap
      (TensorProduct.map p p (Coalgebra.comul a.val)) = Coalgebra.comul a.val := by
  let i := (hopfSubgroupCoinvariants q).val.toLinearMap
  let f := (hopfSubgroupRightCoaction q).toLinearMap -
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap
  have hr : TensorProduct.map (LinearMap.id : A →ₗ[R] A) (i.comp p)
      (Coalgebra.comul a.val) = Coalgebra.comul a.val :=
    tensorSubmoduleRetraction_fixed (hopfSubgroupCoinvariants q).toSubmodule f
      (hopfSubgroupCoinvariants_kernel q) p hp _
      (hopfCoinvariant_comul_right q a.val a.property)
  have hl : TensorProduct.map (i.comp p) (LinearMap.id : A →ₗ[R] A)
      (Coalgebra.comul a.val) = Coalgebra.comul a.val := by
    have h := TensorProduct.map_comm (i.comp p) (LinearMap.id : A →ₗ[R] A)
      (Coalgebra.comul a.val)
    rw [Coalgebra.comm_comul, hr, Coalgebra.comm_comul] at h
    exact h
  exact tensorRetraction_pair_image i p _ hl hr

/-- The actual invariant coordinate algebra has a genuine linear comultiplication whose image is exactly the original comultiplication. Its construction uses a proved PID retraction, with no tensor-descent assumption. -/
theorem hopfCoinvariant_exists_comultiplication (q : A →ₐc[R] B) :
    ∃ d : hopfSubgroupCoinvariants q →ₗ[R]
        (hopfSubgroupCoinvariants q) ⊗[R] (hopfSubgroupCoinvariants q),
      (TensorProduct.map (hopfSubgroupCoinvariants q).val.toLinearMap
        (hopfSubgroupCoinvariants q).val.toLinearMap).comp d =
      Coalgebra.comul.comp (hopfSubgroupCoinvariants q).val.toLinearMap := by
  obtain ⟨p, hp⟩ := hopfSubgroupCoinvariants_exists_retraction q
  refine ⟨(TensorProduct.map p p).comp
    (Coalgebra.comul.comp (hopfSubgroupCoinvariants q).val.toLinearMap), ?_⟩
  apply LinearMap.ext
  intro a
  exact hopfCoinvariant_tensor_image q p hp a

end
end Dubon2026
