import Dubon2026.IntegralHopfSubgroupInvariantGalois
import Dubon2026.IntegralHopfInvariantGenericReduced
import Dubon2026.HopfBaseChangePoints

/-! # The genuine generic-fiber points of the original integral subgroup quotient model -/

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

/-- The original point group in the genuine generic-fiber realization of its subgroup quotient. -/
local instance invariantGenericPointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The genuine tensor Hopf structure on the constructed invariant coordinates, with the original base and both tensor factors explicit. -/
abbrev integralHopfSubgroupInvariantGenericHopfAlgebra
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  exact TensorProduct.instHopfAlgebra (R := R) (S := F)
    (A := integralHopfSubgroupInvariantCoordinates X hX) (B := F)

/-- The genuine convolution point group of the original invariant model's actual generic fiber. -/
abbrev integralHopfSubgroupInvariantGenericPointGroup
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantGenericHopfAlgebra X hX
    Group (WithConv (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX →ₐ[F] K)) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  exact commutativeHopfPointsGroup (R := F)
    (A := F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) (B := K)

/-- The literal generic fiber of the actual integral invariant Hopf model has the same genuine point group as the original quotient by the specified subgroup. The equivalence uses the proved original quotient comparison and actual tensor scalar extension. -/
def integralHopfSubgroupInvariantGenericQuotientPoints
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantGenericHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantGenericPointGroup X hX
    (WithConv (A →ₐ[R] K) ⧸ X) ≃*
      WithConv (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX →ₐ[F] K) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantPointGroup X hX
  letI := integralHopfSubgroupInvariantGenericPointGroup X hX
  exact (integralHopfSubgroupInvariantQuotientPoints X hX).trans
    (hopfBaseChangePointsEquiv (R := R) (F := F)
      (A := integralHopfSubgroupInvariantCoordinates X hX) (K := K))

/-- The genuine generic-fiber realization evaluates an original invariant coordinate by its original quotient representative. -/
theorem integralHopfSubgroupInvariantGenericQuotientPoints_mk
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (p : WithConv (A →ₐ[R] K)) (a : integralHopfSubgroupInvariantCoordinates X hX) :
    integralHopfSubgroupInvariantGenericQuotientPoints X hX (QuotientGroup.mk p)
      ((1 : F) ⊗ₜ[R] a) = p a.val := by
  exact (algebraBaseChangePoint_original (F := F)
    (integralHopfSubgroupInvariantQuotientPoints X hX (QuotientGroup.mk p)).ofConv a).trans
      (integralHopfSubgroupInvariantQuotientPoints_mk X hX p a)

/-- The literal generic-fiber point realization intertwines the original quotient Galois action with the genuine field action on the actual generic Hopf coordinate algebra. -/
theorem integralHopfSubgroupInvariantGenericQuotientPoints_galois
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (g : K ≃ₐ[F] K) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantGenericHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantGenericPointGroup X hX
    ∀ z : WithConv (A →ₐ[R] K) ⧸ X,
      integralHopfSubgroupInvariantGenericQuotientPoints X hX
          (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        commutativeHopfPointsAutomorphism
          (A := F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) g
          (integralHopfSubgroupInvariantGenericQuotientPoints X hX z) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantPointGroup X hX
  letI := integralHopfSubgroupInvariantGenericPointGroup X hX
  intro z
  change hopfBaseChangePointsEquiv (R := R) (F := F)
      (A := integralHopfSubgroupInvariantCoordinates X hX) (K := K)
      (integralHopfSubgroupInvariantQuotientPoints X hX
        (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z)) = _
  rw [integralHopfSubgroupInvariantQuotientPoints_galois]
  exact hopfBaseChangePointsEquiv_galois g (integralHopfSubgroupInvariantQuotientPoints X hX z)

end
end Dubon2026
