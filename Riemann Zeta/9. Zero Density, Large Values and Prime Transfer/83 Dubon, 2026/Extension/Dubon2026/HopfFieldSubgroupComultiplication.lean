import Dubon2026.HopfGaloisStablePointClosure
import Dubon2026.FiniteReducedTensorPointSeparation
import Dubon2026.FiniteFreeHopfPoints

/-! # Actual subgroup comultiplication descent over a perfect field -/

namespace Dubon2026
noncomputable section
open WithConv

variable {F A K : Type*} [Field F] [PerfectField F] [CommRing A] [HopfAlgebra F A]
  [Module.Finite F A] [Field K] [Algebra F K] [Normal F K] [IsAlgClosed K]

/-- The original field-valued Hopf point group used in subgroup multiplication. -/
local instance hopfFieldSubgroupPointGroup : Group (WithConv (A →ₐ[F] K)) :=
  commutativeHopfPointsGroup

/-- Over a perfect field, genuine Galois stability and subgroup multiplication force the original comultiplication to vanish in the actual quotient tensor algebra. No descended comultiplication or tensor separation premise is assumed. -/
theorem hopfFieldSubgroup_comultiplication_vanishing
    (X : @Subgroup (WithConv (A →ₐ[F] K)) (commutativeHopfPointsGroup (R := F)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[F] K)), p ∈ X →
      commutativeHopfPointsAutomorphism g p ∈ X) :
    let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[F] K)))
    I ≤ RingHom.ker (((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I)
      (Ideal.Quotient.mkₐ F I)).comp (Bialgebra.comulAlgHom F A)).toRingHom) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite F A
  letI : Finite (WithConv (A →ₐ[F] K)) := finiteFreeHopfPoints_finite
  let I := hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[F] K)))
  let Q := A ⧸ I
  let q₀ : A →ₐ[F] Q := Ideal.Quotient.mkₐ F I
  letI : IsReduced Q := isReduced_of_injective
    (hopfPointsQuotientEvaluation (X : Set (WithConv (A →ₐ[F] K))))
    (hopfPointsQuotientEvaluation_injective (X : Set (WithConv (A →ₐ[F] K))))
  have hclosed := hopfGaloisStablePointSet_eq_vanishing
    (X : Set (WithConv (A →ₐ[F] K))) hX
  have hpoint (p : Q →ₐ[F] K) : toConv (p.comp q₀) ∈ X := by
    change toConv (p.comp q₀) ∈ (X : Set (WithConv (A →ₐ[F] K)))
    rw [hclosed]
    intro a ha
    change p (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  change I ≤ RingHom.ker (((Algebra.TensorProduct.map q₀ q₀).comp
    (Bialgebra.comulAlgHom F A)).toRingHom)
  intro a ha
  change (Algebra.TensorProduct.map q₀ q₀) (Coalgebra.comul a) = 0
  apply finiteReducedTensor_eq_zero_of_point_pairs (K := K)
  intro p q
  have hc : (Algebra.TensorProduct.productMap p q).comp (Algebra.TensorProduct.map q₀ q₀) =
      Algebra.TensorProduct.productMap (p.comp q₀) (q.comp q₀) := by
    apply Algebra.TensorProduct.ext'
    intro b c
    rfl
  calc
    _ = Algebra.TensorProduct.productMap (p.comp q₀) (q.comp q₀) (Coalgebra.comul a) :=
      AlgHom.congr_fun hc _
    _ = (toConv (p.comp q₀) * toConv (q.comp q₀)) a :=
      (AlgHom.convMul_apply (toConv (p.comp q₀)) (toConv (q.comp q₀)) a).symm
    _ = 0 := (hopfPointsVanishingIdeal_mem_iff _ a).mp ha
      ⟨_, X.mul_mem (hpoint p) (hpoint q)⟩

end
end Dubon2026
