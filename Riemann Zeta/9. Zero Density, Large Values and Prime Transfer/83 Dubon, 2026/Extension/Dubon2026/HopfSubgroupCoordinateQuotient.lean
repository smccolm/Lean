import Dubon2026.HopfCoordinateQuotient
import Dubon2026.HopfSubgroupVanishingAntipode
import Dubon2026.HopfPointsCoordinateQuotientFree
import Dubon2026.FiniteFreeHopfPoints

/-! # The subgroup coordinate quotient, conditional on actual comultiplication descent -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing K] [Algebra R K]

/-- The original point group for the coordinate Hopf quotient. -/
local instance hopfSubgroupCoordinatePointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- Original subgroup inversion and identity derive antipode and counit stability. The remaining explicit comultiplication condition constructs the actual coordinate Hopf quotient. -/
abbrev hopfSubgroupCoordinateQuotient (hinj : Function.Injective (algebraMap R K))
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hd : let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
      I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
        (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom)) :
    HopfAlgebra R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :=
  hopfCoordinateQuotient _ hd
    (fun a ha => hopfSubgroupVanishingIdeal_counit hinj X a ha)
    (fun a ha => hopfSubgroupVanishingIdeal_antipode X a ha)

end

noncomputable section
open scoped TensorProduct

variable {R A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
  [Field K] [Algebra R K] [FaithfulSMul R K]

/-- The original point group in the finite-coordinate quotient application. -/
local instance hopfSubgroupCoordinateFinitePointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- Conditional on the displayed original comultiplication vanishing, the genuine subgroup coordinate quotient has finite free coordinates and a finite actual point group with its coordinate-rank bound. -/
theorem hopfSubgroupCoordinateQuotient_finitePoints
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hd : let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
      I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
        (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom)) :
    let Q := A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
    letI := hopfSubgroupCoordinateQuotient (FaithfulSMul.algebraMap_injective R K) X hd
    Module.Finite R Q ∧ Module.Free R Q ∧
      Finite (WithConv (Q →ₐ[R] K)) ∧
        Nat.card (WithConv (Q →ₐ[R] K)) ≤ Module.finrank R Q := by
  letI := hopfSubgroupCoordinateQuotient (FaithfulSMul.algebraMap_injective R K) X hd
  obtain ⟨hfinite, hfree⟩ := hopfPointsCoordinateQuotient_finite_free
    (X : Set (WithConv (A →ₐ[R] K)))
  letI := hfinite
  letI := hfree
  exact ⟨hfinite, hfree, finiteFreeHopfPoints_finite, finiteFreeHopfPoints_card_le⟩

end
end Dubon2026
