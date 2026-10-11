import Dubon2026.LocalizedHopfPointClosure
import Dubon2026.LocalizedAlgebraPointInjection
import Dubon2026.GenericFiberTensorCoordinates
import Dubon2026.FiniteReducedTensorPointSeparation
import Dubon2026.HopfPointsCoordinateQuotientFree

/-! # Actual integral subgroup comultiplication descent -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct nonZeroDivisors

variable {R F A K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
  [Normal F K] [IsAlgClosed K]

/-- The original integral Hopf point group used in the subgroup descent proof. -/
local instance integralHopfSubgroupPointGroup : Group (WithConv (A →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- Over the original PID with perfect fraction field, a genuine Galois-stable point subgroup forces the literal quotient-tensor comultiplication to vanish on its original coordinate ideal. The actual quotient is proved free, its generic fiber reduced, and its tensor coordinates faithful; no comultiplication descent premise remains. -/
theorem integralHopfSubgroup_comultiplication_vanishing
    (X : @Subgroup (WithConv (A →ₐ[R] K)) (commutativeHopfPointsGroup (R := R)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
    I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R I)).comp (Bialgebra.comulAlgHom R A)).toRingHom) := by
  letI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr (by
    rw [IsScalarTower.algebraMap_eq R F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective R F))
  let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K)))
  let Q := A ⧸ I
  let q₀ : A →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  letI : Module.Free R Q := (hopfPointsCoordinateQuotient_finite_free
    (X : Set (WithConv (A →ₐ[R] K)))).2
  letI : IsReduced (F ⊗[R] Q) := localizedAlgebraPoint_isReduced R⁰
    (hopfPointsQuotientEvaluation (X : Set (WithConv (A →ₐ[R] K))))
    (hopfPointsQuotientEvaluation_injective (X : Set (WithConv (A →ₐ[R] K))))
  have hclosed := localizedHopfPointSet_eq_vanishing (F := F)
    (X : Set (WithConv (A →ₐ[R] K))) hX
  have hpoint (p : Q →ₐ[R] K) : toConv (p.comp q₀) ∈ X := by
    change toConv (p.comp q₀) ∈ (X : Set (WithConv (A →ₐ[R] K)))
    rw [hclosed]
    intro a ha
    change p (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  change I ≤ RingHom.ker (((Algebra.TensorProduct.map q₀ q₀).comp
    (Bialgebra.comulAlgHom R A)).toRingHom)
  intro a ha
  change (Algebra.TensorProduct.map q₀ q₀) (Coalgebra.comul a) = 0
  apply genericFiberTensorCoordinates_injective (F := F)
  rw [map_zero]
  apply finiteReducedTensor_eq_zero_of_point_pairs (K := K)
  intro p q
  rw [genericFiberTensorCoordinates_point_pair]
  let p₀ := (AlgHom.liftEquiv R F Q K).symm p
  let q₁ := (AlgHom.liftEquiv R F Q K).symm q
  have hc : (Algebra.TensorProduct.productMap p₀ q₁).comp (Algebra.TensorProduct.map q₀ q₀) =
      Algebra.TensorProduct.productMap (p₀.comp q₀) (q₁.comp q₀) := by
    apply Algebra.TensorProduct.ext'
    intro b c
    rfl
  calc
    _ = Algebra.TensorProduct.productMap (p₀.comp q₀) (q₁.comp q₀) (Coalgebra.comul a) :=
      AlgHom.congr_fun hc _
    _ = (toConv (p₀.comp q₀) * toConv (q₁.comp q₀)) a :=
      (AlgHom.convMul_apply (toConv (p₀.comp q₀)) (toConv (q₁.comp q₀)) a).symm
    _ = 0 := (hopfPointsVanishingIdeal_mem_iff _ a).mp ha
      ⟨_, X.mul_mem (hpoint p₀) (hpoint q₁)⟩

end
end Dubon2026
