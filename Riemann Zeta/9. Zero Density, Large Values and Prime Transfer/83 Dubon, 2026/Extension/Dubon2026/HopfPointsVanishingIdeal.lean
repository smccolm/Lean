import Dubon2026.CommutativeHopfPointsGroup
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual coordinate ideal vanishing on a specified set of Hopf points -/

namespace Dubon2026
noncomputable section

variable {R A K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing K] [Algebra R K]

/-- Evaluate each original coordinate at every actual point in the specified set. -/
def hopfPointsEvaluation (X : Set (WithConv (A →ₐ[R] K))) : A →ₐ[R] (X → K) where
  toFun a p := p.val a
  map_one' := funext fun p => p.val.ofConv.map_one
  map_mul' a b := funext fun p => p.val.ofConv.map_mul a b
  map_zero' := funext fun p => p.val.ofConv.map_zero
  map_add' a b := funext fun p => p.val.ofConv.map_add a b
  commutes' r := funext fun p => p.val.ofConv.commutes r

/-- The literal joint evaluation kernel on the specified genuine points. -/
def hopfPointsVanishingIdeal (X : Set (WithConv (A →ₐ[R] K))) : Ideal A :=
  RingHom.ker (hopfPointsEvaluation X).toRingHom

/-- Membership is exactly vanishing of the same original coordinate at every specified point. -/
theorem hopfPointsVanishingIdeal_mem_iff (X : Set (WithConv (A →ₐ[R] K))) (a : A) :
    a ∈ hopfPointsVanishingIdeal X ↔ ∀ p : X, p.val a = 0 := by
  change (fun p : X => p.val a) = 0 ↔ _
  exact ⟨fun h p => congrFun h p, fun h => funext h⟩

/-- The quotient by actual point vanishing maps to the actual product of point-value fields. -/
def hopfPointsQuotientEvaluation (X : Set (WithConv (A →ₐ[R] K))) :
    A ⧸ hopfPointsVanishingIdeal X →ₐ[R] (X → K) :=
  Ideal.kerLiftAlg (hopfPointsEvaluation X)

/-- This is an injection of the genuine coordinate quotient, derived from its literal joint kernel. -/
theorem hopfPointsQuotientEvaluation_injective (X : Set (WithConv (A →ₐ[R] K))) :
    Function.Injective (hopfPointsQuotientEvaluation X) := by
  exact Ideal.kerLiftAlg_injective (hopfPointsEvaluation X)

/-- Quotient evaluation preserves every original coordinate value. -/
theorem hopfPointsQuotientEvaluation_mk (X : Set (WithConv (A →ₐ[R] K))) (a : A) (p : X) :
    hopfPointsQuotientEvaluation X (Ideal.Quotient.mk (hopfPointsVanishingIdeal X) a) p = p.val a := by
  rfl

end
end Dubon2026
