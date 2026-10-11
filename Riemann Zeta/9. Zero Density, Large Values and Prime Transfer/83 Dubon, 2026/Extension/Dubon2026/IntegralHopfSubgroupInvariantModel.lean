import Dubon2026.IntegralHopfSubgroupPointEquivalence
import Dubon2026.HopfPointQuotientGeometricReduced
import Dubon2026.IntegralHopfCoinvariantQuotientPoints

/-! # The actual integral invariant Hopf model for a given original subgroup -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Module.Flat R K] [Normal F K] [IsAlgClosed K]

/-- The actual commutative original point group in the subgroup quotient model. -/
local instance subgroupInvariantModelPointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The original invariant coordinate subalgebra for the already constructed genuine integral model of the specified Galois-stable subgroup. -/
def integralHopfSubgroupInvariantCoordinates
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) : Subalgebra R A := by
  letI := integralHopfSubgroupQuotient X hX
  exact hopfSubgroupCoinvariants (integralHopfSubgroupQuotientMap X hX)

/-- Construct the actual Hopf algebra on the original invariant coordinates for the given subgroup. Finite freeness of its actual subgroup coordinate quotient is derived, not assumed. -/
abbrev integralHopfSubgroupInvariantHopfAlgebra
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    HopfAlgebra R (integralHopfSubgroupInvariantCoordinates X hX) := by
  letI := integralHopfSubgroupQuotient X hX
  letI : Module.Free R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :=
    (integralHopfSubgroupQuotient_finitePoints X hX).2.1
  exact hopfCoinvariantHopfAlgebra (integralHopfSubgroupQuotientMap X hX)

omit [Module.Flat R K] in
/-- The actual subgroup-invariant model has finite free original coordinates, with the same original comultiplication and antipode diagrams. -/
theorem integralHopfSubgroupInvariantHopfAlgebra_finite_free
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    let C := integralHopfSubgroupInvariantCoordinates X hX
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    Module.Finite R C ∧ Module.Free R C ∧
      (Algebra.TensorProduct.map C.val C.val).comp (Bialgebra.comulAlgHom R C) =
        (Bialgebra.comulAlgHom R A).comp C.val ∧
      C.val.toLinearMap.comp (HopfAlgebra.antipode R) =
        (HopfAlgebra.antipode R).comp C.val.toLinearMap := by
  letI := integralHopfSubgroupQuotient X hX
  letI : Module.Free R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :=
    (integralHopfSubgroupQuotient_finitePoints X hX).2.1
  exact hopfCoinvariantHopfAlgebra_finite_free (integralHopfSubgroupQuotientMap X hX)

omit [Module.Free R A] [Module.Flat R K] in
/-- The point image of the genuine constructed subgroup coordinate map is exactly the original specified subgroup. -/
theorem integralHopfSubgroupQuotientMap_points_range
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupQuotient X hX
    letI : Group (WithConv ((A ⧸ hopfPointsVanishingIdeal
      (X : Set (WithConv (A →ₐ[R] K)))) →ₐ[R] K)) := commutativeHopfPointsGroup
    (hopfPointsRestriction (K := K) (integralHopfSubgroupQuotientMap X hX)).range = X := by
  letI := integralHopfSubgroupQuotient X hX
  letI : Group (WithConv ((A ⧸ hopfPointsVanishingIdeal
    (X : Set (WithConv (A →ₐ[R] K)))) →ₐ[R] K)) := commutativeHopfPointsGroup
  apply SetLike.coe_injective
  exact integralHopfSubgroupQuotient_point_range X hX

/-- The actual convolution point group of the constructed original invariant Hopf coordinates. -/
abbrev integralHopfSubgroupInvariantPointGroup
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    Group (WithConv (integralHopfSubgroupInvariantCoordinates X hX →ₐ[R] K)) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  exact commutativeHopfPointsGroup

/-- The actual point group of the constructed integral invariant Hopf model realizes precisely the quotient by the original specified Galois-stable subgroup. Reducedness of the subgroup geometric coordinates is derived from the actual point quotient. -/
def integralHopfSubgroupInvariantQuotientPoints
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantPointGroup X hX
    (WithConv (A →ₐ[R] K) ⧸ X) ≃*
      WithConv (integralHopfSubgroupInvariantCoordinates X hX →ₐ[R] K) := by
  letI := integralHopfSubgroupQuotient X hX
  letI : Module.Free R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :=
    (integralHopfSubgroupQuotient_finitePoints X hX).2.1
  letI := hopfPointQuotient_geometric_isReduced (F := F) (X : Set (WithConv (A →ₐ[R] K)))
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantPointGroup X hX
  exact (QuotientGroup.quotientMulEquivOfEq
    (integralHopfSubgroupQuotientMap_points_range X hX).symm).trans
      (integralHopfCoinvariantQuotientPoints (integralHopfSubgroupQuotientMap X hX))

/-- The original quotient point realizes each actual invariant coordinate by the same original representative evaluation. -/
theorem integralHopfSubgroupInvariantQuotientPoints_mk
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (p : WithConv (A →ₐ[R] K)) (a : integralHopfSubgroupInvariantCoordinates X hX) :
    integralHopfSubgroupInvariantQuotientPoints X hX (QuotientGroup.mk p) a = p a.val := by
  rfl

end
end Dubon2026
