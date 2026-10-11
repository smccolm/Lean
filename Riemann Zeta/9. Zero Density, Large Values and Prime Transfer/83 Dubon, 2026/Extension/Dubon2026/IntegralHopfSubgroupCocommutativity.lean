import Dubon2026.IntegralHopfSubgroupInvariantModel
import Dubon2026.BialgebraCocommutativeDescent

/-! # Genuine commutative group coordinates for the original subgroup and quotient models -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Normal F K] [IsAlgClosed K]

/-- The original commutative point group for the genuine subgroup models. -/
local instance subgroupCocommutativityPoints : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

omit [Module.Free R A] in
/-- The constructed integral subgroup Hopf quotient is genuinely cocommutative, by the actual original surjective coordinate map. -/
theorem integralHopfSubgroupQuotient_isCocomm
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupQuotient X hX
    Coalgebra.IsCocomm R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) := by
  letI := integralHopfSubgroupQuotient X hX
  exact bialgebraIsCocomm_of_surjective (integralHopfSubgroupQuotientMap X hX)
    Ideal.Quotient.mk_surjective

/-- The actual integral invariant-coordinate Hopf model is cocommutative, by its proved finite free coordinates and faithful original coordinate inclusion. -/
theorem integralHopfSubgroupInvariant_isCocomm
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI : Coalgebra R (integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantHopfAlgebra X hX).toCoalgebra
    Coalgebra.IsCocomm R (integralHopfSubgroupInvariantCoordinates X hX) := by
  letI := integralHopfSubgroupQuotient X hX
  letI : Module.Free R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :=
    (integralHopfSubgroupQuotient_finitePoints X hX).2.1
  let q := integralHopfSubgroupQuotientMap X hX
  letI := hopfCoinvariantHopfAlgebra q
  letI : Module.Free R (hopfSubgroupCoinvariants q) :=
    (hopfSubgroupCoinvariants_finite_free q).2
  exact bialgebraIsCocomm_of_injective (hopfCoinvariantBialgebraInclusion q) Subtype.val_injective

end
end Dubon2026
