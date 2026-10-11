import Dubon2026.HopfCoinvariantTensorImage

/-! # Algebra laws for the actual invariant-coordinate comultiplication -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

/-- Reflect algebra laws through a genuine injective coordinate algebra map. -/
private def algHomOfLinearCoordinateLift {R C D E : Type*} [CommRing R]
    [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    [CommRing E] [Algebra R E]
    (i : D →ₐ[R] E) (hi : Function.Injective i) (f : C →ₗ[R] D)
    (g : C →ₐ[R] E) (h : i.toLinearMap.comp f = g.toLinearMap) : C →ₐ[R] D :=
  AlgHom.ofLinearMap f
    (hi (by
      change i (f 1) = i 1
      rw [show i (f 1) = g 1 from LinearMap.congr_fun h 1, map_one, map_one]))
    (fun x y => hi (by
      change i (f (x * y)) = i (f x * f y)
      rw [show i (f (x * y)) = g (x * y) from LinearMap.congr_fun h (x * y),
        map_mul, map_mul,
        show i (f x) = g x from LinearMap.congr_fun h x,
        show i (f y) = g y from LinearMap.congr_fun h y]))

variable {R A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [CommRing B] [Bialgebra R B] [Module.Free R B]

/-- The actual invariant-coordinate comultiplication is an algebra homomorphism. Its algebra laws follow from the original bialgebra through the proved injective tensor inclusion, and its exact original coordinate diagram is retained. -/
theorem hopfCoinvariant_exists_comulAlgHom (q : A →ₐc[R] B) :
    ∃ d : hopfSubgroupCoinvariants q →ₐ[R]
        (hopfSubgroupCoinvariants q) ⊗[R] (hopfSubgroupCoinvariants q),
      (Algebra.TensorProduct.map (hopfSubgroupCoinvariants q).val
        (hopfSubgroupCoinvariants q).val).comp d =
      (Bialgebra.comulAlgHom R A).comp (hopfSubgroupCoinvariants q).val := by
  obtain ⟨d, hd⟩ := hopfCoinvariant_exists_comultiplication q
  letI : Module.Free R (hopfSubgroupCoinvariants q) :=
    (hopfSubgroupCoinvariants_finite_free q).2
  let j := Algebra.TensorProduct.map (hopfSubgroupCoinvariants q).val
    (hopfSubgroupCoinvariants q).val
  have hj : Function.Injective j := TensorProduct.map_injective_of_flat_flat
    (hopfSubgroupCoinvariants q).val.toLinearMap
    (hopfSubgroupCoinvariants q).val.toLinearMap
    Subtype.val_injective Subtype.val_injective
  let e := algHomOfLinearCoordinateLift j hj d
    ((Bialgebra.comulAlgHom R A).comp (hopfSubgroupCoinvariants q).val) hd
  refine ⟨e, ?_⟩
  apply AlgHom.toLinearMap_injective
  exact hd

end
end Dubon2026
