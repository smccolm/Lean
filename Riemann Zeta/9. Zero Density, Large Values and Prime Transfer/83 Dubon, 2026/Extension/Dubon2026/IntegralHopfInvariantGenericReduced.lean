import Dubon2026.IntegralHopfSubgroupInvariantModel
import Mathlib.RingTheory.Flat.Localization

/-! # Reduced and formally etale generic fiber of the actual integral invariant model -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A] [IsReduced (F ⊗[R] A)]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Normal F K] [IsAlgClosed K]

/-- The original commutative point group in the generic invariant-model comparison. -/
local instance invariantGenericReducedPointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

omit [Module.Free R A] in
/-- The original invariant model has reduced generic fiber, since flat extension of its actual coordinate inclusion injects into the same reduced original generic coordinate algebra. -/
theorem integralHopfSubgroupInvariant_generic_isReduced
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    IsReduced (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) := by
  letI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  exact reducedScalarExtension_subalgebra (S := F) (integralHopfSubgroupInvariantCoordinates X hX)

/-- The genuine generic fiber of the constructed integral invariant model is formally etale over the original perfect field, using its proved finite coordinates and derived reducedness. -/
theorem integralHopfSubgroupInvariant_generic_formallyEtale
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    Algebra.FormallyEtale F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) := by
  letI : Module.Finite R (integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).1
  letI := integralHopfSubgroupInvariant_generic_isReduced X hX
  exact finiteReducedAlgebra_formallyEtale (F := F)

end
end Dubon2026
