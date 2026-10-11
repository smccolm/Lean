import Dubon2026.IntegralHopfSubgroupPointEquivalence
import Dubon2026.HopfBaseChangePoints

/-! # The genuine generic-fiber points of the integral subgroup model -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Normal F K] [IsAlgClosed K]

/-- The original point group whose subgroup is realized by the actual integral model. -/
local instance integralHopfGenericPointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- Compose genuine base change and original quotient restriction to identify the actual generic-fiber point group with the original subgroup. -/
def integralHopfSubgroupGenericPointsEquiv
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    let Q := A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
    letI := integralHopfSubgroupQuotient X hX
    WithConv (F ⊗[R] Q →ₐ[F] K) ≃* X := by
  letI := integralHopfSubgroupQuotient X hX
  exact (hopfBaseChangePointsEquiv (R := R) (F := F) (K := K)).symm.trans
    (integralHopfSubgroupPointsEquiv X hX)

/-- The true generic point comparison evaluates the original quotient coordinate after its literal scalar extension. -/
theorem integralHopfSubgroupGenericPointsEquiv_apply
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (p : WithConv (F ⊗[R] (A ⧸ hopfPointsVanishingIdeal
      (X : Set (WithConv (A →ₐ[R] K)))) →ₐ[F] K)) (a : A) :
    (integralHopfSubgroupGenericPointsEquiv X hX p).val a =
      p (1 ⊗ₜ[R] Ideal.Quotient.mk
        (hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) a) := by
  rfl

/-- The exact generic-fiber point equivalence intertwines the genuine field Galois action with its action on the original subgroup coordinates. -/
theorem integralHopfSubgroupGenericPointsEquiv_galois
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (g : K ≃ₐ[F] K) :
    let Q := A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
    letI := integralHopfSubgroupQuotient X hX
    ∀ p : WithConv (F ⊗[R] Q →ₐ[F] K),
      (integralHopfSubgroupGenericPointsEquiv X hX
        (commutativeHopfPointsAutomorphism g p)).val =
      commutativeHopfPointsAutomorphism (g.restrictScalars R)
        (integralHopfSubgroupGenericPointsEquiv X hX p).val := by
  dsimp only
  intro p
  apply WithConv.ext
  ext a
  rfl

end
end Dubon2026
