import Dubon2026.IntegralHopfSubgroupComultiplication
import Dubon2026.HopfSubgroupCoordinateQuotient

/-! # The actual integral Hopf quotient of a Galois-stable point subgroup -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct nonZeroDivisors

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Normal F K] [IsAlgClosed K]

/-- The original integral point group for the actual subgroup Hopf quotient. -/
local instance integralHopfQuotientPointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- Construct the Hopf algebra on the original subgroup coordinate quotient using proved integral comultiplication descent and genuine subgroup antipode and counit stability. -/
abbrev integralHopfSubgroupQuotient
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    HopfAlgebra R (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) :=
  hopfSubgroupCoordinateQuotient (by
    rw [IsScalarTower.algebraMap_eq R F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective R F)) X
    (integralHopfSubgroup_comultiplication_vanishing X hX)

/-- The constructed genuine integral Hopf quotient has finite free coordinates and a finite actual point group. No quotient comultiplication condition is assumed. -/
theorem integralHopfSubgroupQuotient_finitePoints
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    let Q := A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
    letI := integralHopfSubgroupQuotient X hX
    Module.Finite R Q ∧ Module.Free R Q ∧ Finite (WithConv (Q →ₐ[R] K)) ∧
      Nat.card (WithConv (Q →ₐ[R] K)) ≤ Module.finrank R Q := by
  letI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr (by
    rw [IsScalarTower.algebraMap_eq R F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective R F))
  exact hopfSubgroupCoordinateQuotient_finitePoints X
    (integralHopfSubgroup_comultiplication_vanishing X hX)

omit [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsAlgClosed K] in
/-- The genuine quotient points restrict to exactly the original Galois-stable subgroup, with both directions proved by original point closure and actual quotient lifts. -/
theorem integralHopfSubgroupQuotient_point_range
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
    Set.range (fun p : WithConv (A ⧸ I →ₐ[R] K) =>
      toConv (p.ofConv.comp (Ideal.Quotient.mkₐ R I))) =
        (X : Set (WithConv (A →ₐ[R] K))) := by
  let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
  have hc := localizedHopfPointSet_eq_vanishing (F := F)
    (X : Set (WithConv (A →ₐ[R] K))) hX
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply (Set.ext_iff.mp hc _).mpr
    intro a ha
    change q (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro hp
    let q : A ⧸ I →ₐ[R] K := Ideal.Quotient.liftₐ I p.ofConv
      (fun a ha => (hopfPointsVanishingIdeal_mem_iff _ a).mp ha ⟨p, hp⟩)
    refine ⟨toConv q, ?_⟩
    apply WithConv.ext
    ext a
    rfl

end
end Dubon2026
