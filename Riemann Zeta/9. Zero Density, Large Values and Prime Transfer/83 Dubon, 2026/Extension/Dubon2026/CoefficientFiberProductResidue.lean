import Dubon2026.LocalCoefficientFiberProduct
import Dubon2026.SurjectiveLocalResidue
import Dubon2026.LocalCoefficientReduction

/-! # The actual original coefficient algebra and residue field of its genuine fiber product -/

namespace Dubon2026
noncomputable section

variable {O A B C : Type*} [CommRing O] [CommRing A] [CommRing B] [CommRing C]
  [Algebra O A] [Algebra O B] [Algebra O C]

/-- The compatible original diagonal coefficient map into the actual pair ring. -/
def coefficientFiberProductAlgebraMap (f : A →ₐ[O] C) (g : B →ₐ[O] C) :
    O →+* CoefficientFiberProduct f.toRingHom g.toRingHom where
  toFun o := ⟨(algebraMap O A o, algebraMap O B o), (f.commutes o).trans (g.commutes o).symm⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero _) (map_zero _)
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (map_one _) (map_one _)
  map_add' x y := by
    apply Subtype.ext
    exact Prod.ext (map_add _ x y) (map_add _ x y)
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext (map_mul _ x y) (map_mul _ x y)

/-- The genuine original coefficient algebra structure on the same compatible-pair ring. -/
abbrev coefficientFiberProductAlgebra (f : A →ₐ[O] C) (g : B →ₐ[O] C) :
    Algebra O (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
  (coefficientFiberProductAlgebraMap f g).toAlgebra

/-- The actual first projection retains the original coefficient algebra structure. -/
def coefficientFiberProductFstAlgHom (f : A →ₐ[O] C) (g : B →ₐ[O] C) :
    (letI := coefficientFiberProductAlgebra f g
     CoefficientFiberProduct f.toRingHom g.toRingHom →ₐ[O] A) := by
  letI := coefficientFiberProductAlgebra f g
  exact { coefficientFiberProductFst f.toRingHom g.toRingHom with commutes' := fun _ => rfl }

/-- The actual second projection retains the original coefficient algebra structure. -/
def coefficientFiberProductSndAlgHom (f : A →ₐ[O] C) (g : B →ₐ[O] C) :
    (letI := coefficientFiberProductAlgebra f g
     CoefficientFiberProduct f.toRingHom g.toRingHom →ₐ[O] B) := by
  letI := coefficientFiberProductAlgebra f g
  exact { coefficientFiberProductSnd f.toRingHom g.toRingHom with commutes' := fun _ => rfl }

/-- The two genuine original algebra projections have equal composites to the actual common coefficient algebra. -/
theorem coefficientFiberProductAlgHom_compatible (f : A →ₐ[O] C) (g : B →ₐ[O] C) :
    (letI := coefficientFiberProductAlgebra f g
     f.comp (coefficientFiberProductFstAlgHom f g) =
       g.comp (coefficientFiberProductSndAlgHom f g)) := by
  letI := coefficientFiberProductAlgebra f g
  apply AlgHom.ext
  intro x
  exact x.property

variable [IsLocalRing O] [IsLocalRing A]

/-- The true residue field of the original coefficient fiber product is the original common residue field, via its proved surjective local first projection. -/
def coefficientFiberProductResidueEquiv (f : A →ₐ[O] C) (g : B →ₐ[O] C)
    [IsLocalHom g.toRingHom] (hg : Function.Surjective g)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     IsLocalRing.ResidueField (CoefficientFiberProduct f.toRingHom g.toRingHom) ≃ₐ[O]
       IsLocalRing.ResidueField O) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  let π := coefficientFiberProductFstAlgHom f g
  letI : IsLocalHom π.toRingHom := coefficientFiberProductFst_isLocalHom f.toRingHom g.toRingHom
  exact (surjectiveLocalResidueAlgEquiv π
    (coefficientFiberProductFst_surjective f.toRingHom g.toRingHom hg)).trans eA

/-- The actual residue equivalence agrees on every original compatible coefficient pair with the original first coefficient reduction. -/
theorem coefficientFiberProductResidueEquiv_residue (f : A →ₐ[O] C) (g : B →ₐ[O] C)
    [IsLocalHom g.toRingHom] (hg : Function.Surjective g)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     ∀ x : CoefficientFiberProduct f.toRingHom g.toRingHom,
       coefficientFiberProductResidueEquiv f g hg eA (IsLocalRing.residue _ x) =
         eA (IsLocalRing.residue A x.val.1)) := by
  intro x
  rfl

/-- The whole genuine fiber-product residue reduction is the original first reduction after the actual first algebra projection. -/
theorem coefficientFiberProductReduction_fst (f : A →ₐ[O] C) (g : B →ₐ[O] C)
    [IsLocalHom g.toRingHom] (hg : Function.Surjective g)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA) =
       (localCoefficientReduction eA).comp (coefficientFiberProductFstAlgHom f g)) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  apply AlgHom.ext
  intro x
  rfl

end
end Dubon2026
