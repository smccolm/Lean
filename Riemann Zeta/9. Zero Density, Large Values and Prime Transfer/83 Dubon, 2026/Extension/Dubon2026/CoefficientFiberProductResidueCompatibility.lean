import Dubon2026.CoefficientFiberProductResidue

/-! # Both actual original fiber-product projections preserve the fixed original residue field -/

namespace Dubon2026
noncomputable section

variable {O A B : Type*} [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A]
  [CommRing B] [IsLocalRing B] [Algebra O B]

/-- An actual original coefficient morphism preserving the genuine residue identifications reflects units. -/
theorem originalResiduePreserving_isLocalHom
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (k : A →ₐ[O] B)
    (hres : (localCoefficientReduction eB).comp k = localCoefficientReduction eA) :
    IsLocalHom k.toRingHom := by
  constructor
  intro x hx
  apply (localCoefficientReduction_ne_zero_iff eA x).mp
  have heq : localCoefficientReduction eB (k x) = localCoefficientReduction eA x :=
    DFunLike.congr_fun hres x
  rw [← heq]
  exact (localCoefficientReduction_ne_zero_iff eB (k x)).mpr hx

variable {C : Type*} [CommRing C] [IsLocalRing C] [Algebra O C]

/-- The true original fiber-product residue also equals reduction after the actual second algebra projection, using both original coefficient residue compatibilities. -/
theorem coefficientFiberProductReduction_snd
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA) =
       (localCoefficientReduction eB).comp (coefficientFiberProductSndAlgHom f g)) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  rw [coefficientFiberProductReduction_fst f g hg eA]
  apply AlgHom.ext
  intro x
  change localCoefficientReduction eA x.val.1 = localCoefficientReduction eB x.val.2
  calc
    _ = localCoefficientReduction eC (f x.val.1) :=
      (DFunLike.congr_fun hfres x.val.1).symm
    _ = localCoefficientReduction eC (g x.val.2) :=
      congrArg (localCoefficientReduction eC) x.property
    _ = _ := DFunLike.congr_fun hgres x.val.2

end
end Dubon2026
