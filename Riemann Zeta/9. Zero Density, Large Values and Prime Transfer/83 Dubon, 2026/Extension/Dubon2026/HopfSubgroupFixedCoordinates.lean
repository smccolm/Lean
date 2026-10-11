import Dubon2026.HopfCoinvariantPointTranslations
import Dubon2026.HopfPointsRestriction
import Dubon2026.FiniteFreeHopfPoints
import Dubon2026.FiniteReducedAlgebraPointSeparation
import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-! # Actual subgroup point action and the literal invariant coordinates -/

namespace Dubon2026
noncomputable section
open WithConv

variable {K A B : Type*} [Field K] [CommRing A] [HopfAlgebra K A]
  [CommRing B] [HopfAlgebra K B]

/-- The genuine original subgroup-coordinate point group. -/
local instance hopfFixedCoordinatePointGroup : Group (WithConv (B →ₐ[K] K)) :=
  commutativeHopfPointsGroup

/-- Restrict original subgroup points and apply their actual original coordinate translations. -/
def hopfSubgroupTranslationAction (q : A →ₐc[K] B) :
    WithConv (B →ₐ[K] K) →* (A ≃ₐ[K] A) :=
  hopfPointTranslationAction.comp (hopfPointsRestriction q)

/-- The actual subgroup point group acts on the original coordinate ring through the genuine translation algebra automorphisms. -/
abbrev hopfSubgroupTranslationMulSemiringAction (q : A →ₐc[K] B) :
    MulSemiringAction (WithConv (B →ₐ[K] K)) A :=
  MulSemiringAction.compHom A (hopfSubgroupTranslationAction q)

/-- The actual subgroup coordinate action commutes with the original scalar field. -/
theorem hopfSubgroupTranslationScalarComm (q : A →ₐc[K] B) :
    letI := hopfSubgroupTranslationMulSemiringAction q
    SMulCommClass (WithConv (B →ₐ[K] K)) K A := by
  letI := hopfSubgroupTranslationMulSemiringAction q
  exact ⟨fun p s a => (hopfSubgroupTranslationAction q p).toLinearEquiv.map_smul s a⟩

/-- The actual subgroup action evaluates as translation by the same original restricted point. -/
theorem hopfSubgroupTranslationAction_apply (q : A →ₐc[K] B)
    (p : WithConv (B →ₐ[K] K)) (a : A) :
    letI := hopfSubgroupTranslationMulSemiringAction q
    p • a = hopfPointTranslation (toConv (p.ofConv.comp q.toAlgHom)) a := by
  rfl

/-- For the original finite reduced subgroup coordinates over the original algebraically closed field, literal coaction coinvariants are precisely the fixed subalgebra of the actual subgroup point action. Genuine point separation supplies the needed evaluation injection. -/
theorem hopfSubgroupCoinvariants_eq_fixed [IsAlgClosed K] [Module.Finite K B] [IsReduced B]
    (q : A →ₐc[K] B) :
    letI := hopfSubgroupTranslationMulSemiringAction q
    letI := hopfSubgroupTranslationScalarComm q
    hopfSubgroupCoinvariants q = FixedPoints.subalgebra K A (WithConv (B →ₐ[K] K)) := by
  letI := hopfSubgroupTranslationMulSemiringAction q
  letI := hopfSubgroupTranslationScalarComm q
  letI : Finite (WithConv (B →ₐ[K] K)) := finiteFreeHopfPoints_finite
  have hp : Function.Injective (fun b : B => fun p : WithConv (B →ₐ[K] K) => p b) := by
    intro b c h
    apply sub_eq_zero.mp
    apply finiteReducedAlgebra_eq_zero_of_points (F := K) (K := K)
    intro p
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun h (toConv p))
  apply Subalgebra.ext
  intro a
  change a ∈ hopfSubgroupCoinvariants q ↔
    ∀ p : WithConv (B →ₐ[K] K), p • a = a
  simp only [hopfSubgroupTranslationAction_apply]
  exact hopfCoinvariant_iff_pointTranslations (ι := WithConv (B →ₐ[K] K)) q
    (fun p : WithConv (B →ₐ[K] K) => p.ofConv) hp a

end
end Dubon2026
