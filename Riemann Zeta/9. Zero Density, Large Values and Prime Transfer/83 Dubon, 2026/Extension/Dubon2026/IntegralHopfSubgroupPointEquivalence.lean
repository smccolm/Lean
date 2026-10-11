import Dubon2026.IntegralHopfSubgroupQuotient
import Dubon2026.HopfPointsRestriction

/-! # Actual quotient points and the original subgroup, with their Galois action -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Normal F K] [IsAlgClosed K]

/-- The same original integral point group in the exact quotient point comparison. -/
local instance integralHopfPointEquivalenceGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- The original quotient coordinate map is a genuine bialgebra homomorphism for the constructed integral subgroup Hopf quotient. -/
def integralHopfSubgroupQuotientMap
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupQuotient X hX
    A →ₐc[R] A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) := by
  letI := integralHopfSubgroupQuotient X hX
  exact BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R _) (by ext a; rfl) (by ext a; rfl)

/-- Construct the actual multiplicative equivalence from the genuine quotient points to the original subgroup by restriction, using the proved exact range and original coordinate surjectivity. -/
def integralHopfSubgroupPointsEquiv
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    letI := integralHopfSubgroupQuotient X hX
    WithConv (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) →ₐ[R] K) ≃* X := by
  letI := integralHopfSubgroupQuotient X hX
  let r := hopfPointsRestriction (K := K) (integralHopfSubgroupQuotientMap X hX)
  have hr : Set.range r = (X : Set (WithConv (A →ₐ[R] K))) :=
    integralHopfSubgroupQuotient_point_range X hX
  let f := r.codRestrict X (fun p => (Set.ext_iff.mp hr (r p)).mp (Set.mem_range_self p))
  apply MulEquiv.ofBijective f
  constructor
  · intro p q hpq
    apply WithConv.ext
    ext b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact congrArg (fun x : X => x.val a) hpq
  · intro x
    have hx : x.val ∈ Set.range r := (Set.ext_iff.mp hr x.val).mpr x.property
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, Subtype.ext hp⟩

/-- The constructed subgroup point equivalence preserves the exact original quotient coordinate evaluation. -/
theorem integralHopfSubgroupPointsEquiv_apply
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (p : WithConv (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) →ₐ[R] K))
    (a : A) :
    (integralHopfSubgroupPointsEquiv X hX p).val a =
      p (Ideal.Quotient.mk (hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))) a) := by
  rfl

/-- The actual quotient point equivalence respects the original Galois action on all original coordinates. -/
theorem integralHopfSubgroupPointsEquiv_galois
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (g : K ≃ₐ[F] K) :
    letI := integralHopfSubgroupQuotient X hX
    ∀ p : WithConv (A ⧸ hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) →ₐ[R] K),
      (integralHopfSubgroupPointsEquiv X hX
        (commutativeHopfPointsAutomorphism (g.restrictScalars R) p)).val =
      commutativeHopfPointsAutomorphism (g.restrictScalars R)
        (integralHopfSubgroupPointsEquiv X hX p).val := by
  intro p
  apply WithConv.ext
  ext a
  rfl

end
end Dubon2026
