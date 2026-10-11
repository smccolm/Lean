import Dubon2026.HopfSubgroupVanishingAntipode

/-! # Original antipode and counit descend to the genuine subgroup coordinate quotient -/

namespace Dubon2026
noncomputable section

variable {R A K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing K] [Algebra R K]

/-- The original Hopf point group for the actual subgroup coordinate quotient. -/
local instance hopfSubgroupQuotientPointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- The original antipode descends along the actual subgroup vanishing ideal by the proved subgroup inverse stability. -/
def hopfSubgroupQuotientAntipode
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R))) :
    A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) →ₐ[R]
      A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) :=
  Ideal.quotientMapₐ _ (commutativeHopfAntipode (R := R))
    (fun a ha => hopfSubgroupVanishingIdeal_antipode X a ha)

/-- Quotient antipode evaluation is the original coordinate antipode followed by the original quotient map. -/
theorem hopfSubgroupQuotientAntipode_mk
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R))) (a : A) :
    hopfSubgroupQuotientAntipode X (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (HopfAlgebra.antipode R a) := by
  rfl

/-- The original counit descends to the actual coordinate quotient using its proved vanishing at the identity point. -/
def hopfSubgroupQuotientCounit (hinj : Function.Injective (algebraMap R K))
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R))) :
    A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom R A)
    (fun a ha => hopfSubgroupVanishingIdeal_counit hinj X a ha)

/-- The descended counit evaluates the same original coordinate counit. -/
theorem hopfSubgroupQuotientCounit_mk (hinj : Function.Injective (algebraMap R K))
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R))) (a : A) :
    hopfSubgroupQuotientCounit hinj X (Ideal.Quotient.mk _ a) = Coalgebra.counit (R := R) a := by
  rfl

end
end Dubon2026
