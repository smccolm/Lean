import Dubon2026.HopfPointsRestriction
import Dubon2026.FiniteFreeHopfPoints
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Genuine coefficient automorphisms on the original quotient point group -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B K : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A] [CommRing B] [HopfAlgebra R B]
  [Field K] [Algebra R K]

/-- The actual original commutative point group used to form the genuine subgroup quotient. -/
local instance coefficientQuotientSourcePointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The actual subgroup coordinate point group for the same original restriction map. -/
local instance coefficientQuotientSubgroupPointGroup : Group (WithConv (B →ₐ[R] K)) :=
  commutativeHopfPointsGroup

omit [Coalgebra.IsCocomm R A] in
/-- Actual coefficient automorphisms commute with the original subgroup point restriction on every coordinate. -/
theorem hopfPointRestriction_coefficient (q : A →ₐc[R] B) (g : K ≃ₐ[R] K)
    (p : WithConv (B →ₐ[R] K)) :
    commutativeHopfPointsAutomorphism g (hopfPointsRestriction q p) =
      hopfPointsRestriction q (commutativeHopfPointsAutomorphism g p) := by
  apply WithConv.ext
  ext a
  rfl

omit [Coalgebra.IsCocomm R A] in
/-- The image of the actual original subgroup point map is stable under the genuine coefficient automorphism, with equality proved using its original inverse. -/
theorem hopfPointRestriction_range_coefficient (q : A →ₐc[R] B) (g : K ≃ₐ[R] K) :
    (hopfPointsRestriction (K := K) q).range.map
      (commutativeHopfPointsAutomorphism (A := A) g).toMonoidHom =
        (hopfPointsRestriction (K := K) q).range := by
  ext p
  constructor
  · rintro ⟨s, ⟨t, rfl⟩, rfl⟩
    exact ⟨commutativeHopfPointsAutomorphism g t,
      (hopfPointRestriction_coefficient q g t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨hopfPointsRestriction q (commutativeHopfPointsAutomorphism g.symm t),
      ⟨_, rfl⟩, ?_⟩
    apply WithConv.ext
    ext a
    exact g.apply_symm_apply (t (q a))

/-- The original coefficient automorphism induces a genuine automorphism of the actual quotient point group. -/
def hopfQuotientPointCoefficientAutomorphism (q : A →ₐc[R] B) (g : K ≃ₐ[R] K) :
    MulAut (WithConv (A →ₐ[R] K) ⧸ (hopfPointsRestriction (K := K) q).range) :=
  QuotientGroup.congr _ _ (commutativeHopfPointsAutomorphism (A := A) g)
    (hopfPointRestriction_range_coefficient q g)

/-- The induced quotient automorphism acts on each original representative by its original coefficient action. -/
theorem hopfQuotientPointCoefficientAutomorphism_mk (q : A →ₐc[R] B) (g : K ≃ₐ[R] K)
    (p : WithConv (A →ₐ[R] K)) :
    hopfQuotientPointCoefficientAutomorphism q g (QuotientGroup.mk p) =
      QuotientGroup.mk (commutativeHopfPointsAutomorphism g p) := by
  rfl

end
end Dubon2026
