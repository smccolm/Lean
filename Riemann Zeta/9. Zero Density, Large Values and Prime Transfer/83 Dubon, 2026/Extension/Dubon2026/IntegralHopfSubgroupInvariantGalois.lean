import Dubon2026.IntegralHopfSubgroupInvariantModel

/-! # Actual Galois action on the original subgroup quotient and its integral invariant model -/

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

/-- The original commutative point group for the same specified subgroup quotient. -/
local instance subgroupInvariantGaloisPointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The genuine Galois automorphism acts on the original quotient by the specified stable subgroup; both directions of stability use the original automorphism and its inverse. -/
def integralHopfSubgroupQuotientGaloisAutomorphism
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (g : K ≃ₐ[F] K) : MulAut (WithConv (A →ₐ[R] K) ⧸ X) := by
  apply QuotientGroup.congr X X (commutativeHopfPointsAutomorphism (g.restrictScalars R))
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hX g t ht
  · intro hp
    refine ⟨commutativeHopfPointsAutomorphism (g.symm.restrictScalars R) p,
      hX g.symm p hp, ?_⟩
    apply WithConv.ext
    ext a
    exact g.apply_symm_apply (p a)

omit [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Module.Finite R A] [Module.Free R A] [Module.Flat R K] [Normal F K] [IsAlgClosed K] in
/-- The original quotient Galois automorphism acts on each original representative by the same original coefficient action. -/
theorem integralHopfSubgroupQuotientGaloisAutomorphism_mk
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)) :
    integralHopfSubgroupQuotientGaloisAutomorphism X hX g (QuotientGroup.mk p) =
      QuotientGroup.mk (commutativeHopfPointsAutomorphism (g.restrictScalars R) p) := by
  rfl

/-- The actual quotient by the original specified subgroup is Galois-equivariantly realized by points of the genuine constructed integral invariant Hopf algebra. -/
theorem integralHopfSubgroupInvariantQuotientPoints_galois
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (g : K ≃ₐ[F] K) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI := integralHopfSubgroupInvariantPointGroup X hX
    ∀ z : WithConv (A →ₐ[R] K) ⧸ X,
      integralHopfSubgroupInvariantQuotientPoints X hX
          (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        commutativeHopfPointsAutomorphism (g.restrictScalars R)
          (integralHopfSubgroupInvariantQuotientPoints X hX z) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI := integralHopfSubgroupInvariantPointGroup X hX
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    apply WithConv.ext
    ext a
    rfl

end
end Dubon2026
