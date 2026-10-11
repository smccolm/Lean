import Dubon2026.IntegralHopfInvariantGenericPoints
import Dubon2026.GaloisHopfOriginalBialgEquiv

/-! # Actual generic coordinate realization of the integral subgroup quotient model -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R F A K B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A] [IsReduced (F ⊗[R] A)]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Module.Flat R K] [IsGalois F K] [IsAlgClosed K]
  [CommRing B] [HopfAlgebra F B] [Module.Finite F B] [IsReduced B]

/-- The original commutative point group of the integral ambient model. -/
local instance invariantGenericCoordinateAmbientPoints : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The original point group of the independently specified generic coordinate algebra. -/
local instance invariantGenericCoordinateTargetPoints : Group (WithConv (B →ₐ[F] K)) :=
  commutativeHopfPointsGroup

omit [IsReduced (F ⊗[R] A)] [Module.Finite F B] [IsReduced B] in
/-- The actual generic point comparison inherits equivariance from the original quotient realization and the specified original point comparison. -/
private theorem invariantGenericCoordinatePointComparison_galois
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (e : (WithConv (A →ₐ[R] K) ⧸ X) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (z : WithConv (A →ₐ[R] K) ⧸ X),
      e (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        commutativeHopfPointsAutomorphism g (e z)) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      integralHopfSubgroupInvariantGenericHopfAlgebra X hX
    letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
    letI := integralHopfSubgroupInvariantGenericPointGroup X hX
    letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
    let E := integralHopfSubgroupInvariantGenericQuotientPoints X hX
    ∀ (g : K ≃ₐ[F] K)
      (p : WithConv (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX →ₐ[F] K)),
      (E.symm.trans e) (commutativeHopfPointsAutomorphism g p) =
        commutativeHopfPointsAutomorphism g ((E.symm.trans e) p) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
  letI := integralHopfSubgroupInvariantGenericPointGroup X hX
  letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
  let E := integralHopfSubgroupInvariantGenericQuotientPoints X hX
  dsimp only
  intro g p
  have h : E.symm (commutativeHopfPointsAutomorphism g p) =
      integralHopfSubgroupQuotientGaloisAutomorphism X hX g (E.symm p) := by
    apply E.injective
    rw [E.apply_symm_apply, integralHopfSubgroupInvariantGenericQuotientPoints_galois,
      E.apply_symm_apply]
  change e (E.symm (commutativeHopfPointsAutomorphism g p)) = _
  rw [h]
  exact he g (E.symm p)

/-- Construct the original-field coordinate equivalence from an actual Galois-equivariant point comparison. The source is the independently specified finite reduced generic Hopf algebra; the target is the genuine generic fiber of the constructed finite free integral invariant model. -/
def integralHopfSubgroupInvariantGenericCoordinateEquiv
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (e : (WithConv (A →ₐ[R] K) ⧸ X) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (z : WithConv (A →ₐ[R] K) ⧸ X),
      e (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        commutativeHopfPointsAutomorphism g (e z)) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      integralHopfSubgroupInvariantGenericHopfAlgebra X hX
    letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
    letI := integralHopfSubgroupInvariantGenericPointGroup X hX
    letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
    B ≃ₐc[F] F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
  letI := integralHopfSubgroupInvariantGenericPointGroup X hX
  letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
  letI : Module.Finite R (integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).1
  letI : @Module.Finite F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) _ _
      (@Algebra.toModule F _ _ _
        (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra) :=
    Module.Finite.base_change (R := R) (A := F) (M := integralHopfSubgroupInvariantCoordinates X hX)
  letI := integralHopfSubgroupInvariant_generic_isReduced X hX
  exact galoisHopfOriginalBialgEquiv (F := F)
    (A := F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) (B := B) (K := K)
    ((integralHopfSubgroupInvariantGenericQuotientPoints X hX).symm.trans e)
    (invariantGenericCoordinatePointComparison_galois X hX e he)

/-- The constructed generic coordinate equivalence realizes the specified original quotient point comparison on every original generic coordinate. -/
theorem integralHopfSubgroupInvariantGenericCoordinateEquiv_eval
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (e : (WithConv (A →ₐ[R] K) ⧸ X) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (z : WithConv (A →ₐ[R] K) ⧸ X),
      e (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        commutativeHopfPointsAutomorphism g (e z))
    (b : B) (z : WithConv (A →ₐ[R] K) ⧸ X) :
    integralHopfSubgroupInvariantGenericQuotientPoints X hX z
      (integralHopfSubgroupInvariantGenericCoordinateEquiv X hX e he b) = e z b := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
  letI := integralHopfSubgroupInvariantGenericPointGroup X hX
  letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
  letI : Module.Finite R (integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantHopfAlgebra_finite_free X hX).1
  letI : @Module.Finite F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) _ _
      (@Algebra.toModule F _ _ _
        (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra) :=
    Module.Finite.base_change (R := R) (A := F) (M := integralHopfSubgroupInvariantCoordinates X hX)
  letI := integralHopfSubgroupInvariant_generic_isReduced X hX
  let E := integralHopfSubgroupInvariantGenericQuotientPoints X hX
  have h := galoisHopfOriginalCoordinateEquiv_eval (F := F)
    (A := F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) (B := B) (K := K) (E.symm.trans e)
    (invariantGenericCoordinatePointComparison_galois X hX e he) b (E z)
  change (E z) (galoisHopfOriginalCoordinateEquiv (E.symm.trans e)
    (invariantGenericCoordinatePointComparison_galois X hX e he) b) = e z b
  calc
    _ = (E.symm.trans e) (E z) b := h
    _ = e z b := by
      change e (E.symm (E z)) b = e z b
      rw [E.symm_apply_apply]

/-- The same actual generic coordinate equivalence preserves the genuine Hopf antipodes. -/
theorem integralHopfSubgroupInvariantGenericCoordinateEquiv_antipode
    (X : Subgroup (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X)
    (e : (WithConv (A →ₐ[R] K) ⧸ X) ≃* WithConv (B →ₐ[F] K))
    (he : ∀ (g : K ≃ₐ[F] K) (z : WithConv (A →ₐ[R] K) ⧸ X),
      e (integralHopfSubgroupQuotientGaloisAutomorphism X hX g z) =
        commutativeHopfPointsAutomorphism g (e z)) (b : B) :
    letI := integralHopfSubgroupInvariantHopfAlgebra X hX
    letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      integralHopfSubgroupInvariantGenericHopfAlgebra X hX
    letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
    letI := integralHopfSubgroupInvariantGenericPointGroup X hX
    letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
      (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
    integralHopfSubgroupInvariantGenericCoordinateEquiv X hX e he (HopfAlgebra.antipode F b) =
      HopfAlgebra.antipode F (A := F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX)
        (integralHopfSubgroupInvariantGenericCoordinateEquiv X hX e he b) := by
  letI := integralHopfSubgroupInvariantHopfAlgebra X hX
  letI : HopfAlgebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    integralHopfSubgroupInvariantGenericHopfAlgebra X hX
  letI : Algebra F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toAlgebra
  letI := integralHopfSubgroupInvariantGenericPointGroup X hX
  letI : CoalgebraStruct F (F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX) :=
    (integralHopfSubgroupInvariantGenericHopfAlgebra X hX).toCoalgebraStruct
  exact hopfCoordinateMap_antipode (R := F) (A := B)
    (B := F ⊗[R] integralHopfSubgroupInvariantCoordinates X hX)
    (integralHopfSubgroupInvariantGenericCoordinateEquiv X hX e he).toBialgHom b

end
end Dubon2026
