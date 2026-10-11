import Dubon2026.HopfCoinvariantCoordinateAlgebra
import Dubon2026.HopfCoinvariantPointFibers
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Genuine quotient points of the constructed invariant-coordinate Hopf algebra -/

namespace Dubon2026
noncomputable section
open WithConv

variable {K A B : Type*} [Field K] [IsAlgClosed K]
  [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A] [Module.Finite K A]
  [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [IsReduced B]

/-- Original cocommutativity gives the actual commutative source point group. -/
local instance hopfFieldQuotientSourcePointGroup : CommGroup (WithConv (A →ₐ[K] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The same original subgroup-coordinate point group in the quotient comparison. -/
local instance hopfFieldQuotientSubgroupPointGroup : Group (WithConv (B →ₐ[K] K)) :=
  commutativeHopfPointsGroup

/-- The genuine point group of the actual constructed invariant-coordinate Hopf algebra. -/
abbrev hopfCoinvariantFieldPointGroup (q : A →ₐc[K] B) :
    letI := hopfCoinvariantHopfAlgebra q
    Group (WithConv (hopfSubgroupCoinvariants q →ₐ[K] K)) := by
  letI := hopfCoinvariantHopfAlgebra q
  exact commutativeHopfPointsGroup

/-- Actual coordinate inclusion induces the original point restriction homomorphism into the constructed invariant-coordinate Hopf point group. -/
def hopfCoinvariantFieldPointRestriction (q : A →ₐc[K] B) :
    letI := hopfCoinvariantHopfAlgebra q
    WithConv (A →ₐ[K] K) →* WithConv (hopfSubgroupCoinvariants q →ₐ[K] K) := by
  letI := hopfCoinvariantHopfAlgebra q
  exact hopfPointsRestriction (hopfCoinvariantBialgebraInclusion q)

omit [IsReduced B] in
/-- The actual invariant-coordinate point restriction is surjective, using original geometric point extension across the literal finite-coordinate inclusion. -/
theorem hopfCoinvariantFieldPointRestriction_surjective (q : A →ₐc[K] B) :
    letI := hopfCoinvariantHopfAlgebra q
    Function.Surjective (hopfCoinvariantFieldPointRestriction q) := by
  exact hopfCoinvariantPoints_restriction_surjective q

/-- The kernel of the actual constructed invariant-coordinate point restriction is exactly the image of the original subgroup point map. Both containments consume the proved original point-fiber equivalence. -/
theorem hopfCoinvariantFieldPointRestriction_ker (q : A →ₐc[K] B) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := hopfCoinvariantFieldPointGroup q
    (hopfCoinvariantFieldPointRestriction q).ker = (hopfPointsRestriction (K := K) q).range := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := hopfCoinvariantFieldPointGroup q
  let f := hopfCoinvariantFieldPointRestriction q
  ext p
  constructor
  · intro hp
    change f p = 1 at hp
    have h : p.ofConv.comp (hopfSubgroupCoinvariants q).val =
        (1 : WithConv (A →ₐ[K] K)).ofConv.comp (hopfSubgroupCoinvariants q).val :=
      congrArg WithConv.ofConv (hp.trans f.map_one.symm)
    obtain ⟨s, hs⟩ := (hopfCoinvariantPoints_fiber_orbit q p 1).mp h
    refine ⟨s⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_left hs).symm
  · rintro ⟨s, rfl⟩
    have h := (hopfCoinvariantPoints_fiber_orbit q 1 (hopfPointsRestriction q s)).mpr
      ⟨s, one_mul _⟩
    have he : f 1 = f (hopfPointsRestriction q s) := WithConv.ext h
    change f (hopfPointsRestriction q s) = 1
    rw [← he, map_one]

/-- The original quotient of geometric point groups is multiplicatively equivalent to the genuine point group of the actual constructed invariant-coordinate Hopf algebra. -/
def hopfCoinvariantFieldQuotientPoints (q : A →ₐc[K] B) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := hopfCoinvariantFieldPointGroup q
    (WithConv (A →ₐ[K] K) ⧸ (hopfPointsRestriction (K := K) q).range) ≃*
      WithConv (hopfSubgroupCoinvariants q →ₐ[K] K) := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := hopfCoinvariantFieldPointGroup q
  exact (QuotientGroup.quotientMulEquivOfEq (hopfCoinvariantFieldPointRestriction_ker q).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (hopfCoinvariantFieldPointRestriction q)
      (hopfCoinvariantFieldPointRestriction_surjective q))

/-- The quotient-point equivalence evaluates the same original representative on each genuine invariant coordinate. This retains the actual constructed Hopf point object and its original coordinate map. -/
theorem hopfCoinvariantFieldQuotientPoints_mk (q : A →ₐc[K] B)
    (p : WithConv (A →ₐ[K] K)) (a : hopfSubgroupCoinvariants q) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := hopfCoinvariantFieldPointGroup q
    hopfCoinvariantFieldQuotientPoints q (QuotientGroup.mk p) a = p a.val := by
  rfl

end
end Dubon2026
