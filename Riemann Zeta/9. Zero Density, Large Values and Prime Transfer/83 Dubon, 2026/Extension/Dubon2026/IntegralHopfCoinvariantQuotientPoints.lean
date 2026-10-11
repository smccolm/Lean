import Dubon2026.HopfCoinvariantCoordinateAlgebra
import Dubon2026.IntegralHopfCoinvariantPointFibers
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Genuine quotient points of the constructed original integral invariant Hopf algebra -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct

variable {R K A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field K] [IsAlgClosed K] [Algebra R K] [Module.Flat R K]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
  [IsReduced (K ⊗[R] B)]

/-- Original cocommutativity gives the actual commutative source point group. -/
local instance integralHopfQuotientSourcePointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The same original subgroup-coordinate point group in the quotient comparison. -/
local instance integralHopfQuotientSubgroupPointGroup : Group (WithConv (B →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- The genuine point group of the actual constructed invariant-coordinate Hopf algebra. -/
abbrev integralHopfCoinvariantPointGroup (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    Group (WithConv (hopfSubgroupCoinvariants q →ₐ[R] K)) := by
  letI := hopfCoinvariantHopfAlgebra q
  exact commutativeHopfPointsGroup

/-- Actual coordinate inclusion induces the original point restriction homomorphism into the constructed invariant-coordinate Hopf point group. -/
def integralHopfCoinvariantPointRestriction (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    WithConv (A →ₐ[R] K) →* WithConv (hopfSubgroupCoinvariants q →ₐ[R] K) := by
  letI := hopfCoinvariantHopfAlgebra q
  exact hopfPointsRestriction (hopfCoinvariantBialgebraInclusion q)

omit [Module.Finite R B] [IsReduced (K ⊗[R] B)] in
/-- The actual invariant-coordinate point restriction is surjective, using original geometric point extension across the literal finite-coordinate inclusion. -/
theorem integralHopfCoinvariantPointRestriction_surjective (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    Function.Surjective (integralHopfCoinvariantPointRestriction (K := K) q) := by
  exact integralHopfCoinvariantPoints_restriction_surjective q

/-- The kernel of the actual constructed invariant-coordinate point restriction is exactly the image of the original subgroup point map. Both containments consume the proved original point-fiber equivalence. -/
theorem integralHopfCoinvariantPointRestriction_ker (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := integralHopfCoinvariantPointGroup (K := K) q
    (integralHopfCoinvariantPointRestriction (K := K) q).ker = (hopfPointsRestriction (K := K) q).range := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := integralHopfCoinvariantPointGroup (K := K) q
  let f := integralHopfCoinvariantPointRestriction (K := K) q
  ext p
  constructor
  · intro hp
    change f p = 1 at hp
    have h : p.ofConv.comp (hopfSubgroupCoinvariants q).val =
        (1 : WithConv (A →ₐ[R] K)).ofConv.comp (hopfSubgroupCoinvariants q).val :=
      congrArg WithConv.ofConv (hp.trans f.map_one.symm)
    obtain ⟨s, hs⟩ := (integralHopfCoinvariantPoints_fiber_orbit q p 1).mp h
    refine ⟨s⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_left hs).symm
  · rintro ⟨s, rfl⟩
    have h := (integralHopfCoinvariantPoints_fiber_orbit q 1 (hopfPointsRestriction q s)).mpr
      ⟨s, one_mul _⟩
    have he : f 1 = f (hopfPointsRestriction q s) := WithConv.ext h
    change f (hopfPointsRestriction q s) = 1
    rw [← he, map_one]

/-- The original quotient of original integral-coordinate point groups is multiplicatively equivalent to the genuine point group of the actual constructed invariant-coordinate Hopf algebra. -/
def integralHopfCoinvariantQuotientPoints (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := integralHopfCoinvariantPointGroup (K := K) q
    (WithConv (A →ₐ[R] K) ⧸ (hopfPointsRestriction (K := K) q).range) ≃*
      WithConv (hopfSubgroupCoinvariants q →ₐ[R] K) := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := integralHopfCoinvariantPointGroup (K := K) q
  exact (QuotientGroup.quotientMulEquivOfEq (integralHopfCoinvariantPointRestriction_ker (K := K) q).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (integralHopfCoinvariantPointRestriction (K := K) q)
      (integralHopfCoinvariantPointRestriction_surjective (K := K) q))

/-- The quotient-point equivalence evaluates the same original representative on each genuine invariant coordinate. This retains the actual constructed Hopf point object and its original coordinate map. -/
theorem integralHopfCoinvariantQuotientPoints_mk (q : A →ₐc[R] B)
    (p : WithConv (A →ₐ[R] K)) (a : hopfSubgroupCoinvariants q) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := integralHopfCoinvariantPointGroup (K := K) q
    integralHopfCoinvariantQuotientPoints (K := K) q (QuotientGroup.mk p) a = p a.val := by
  rfl

end
end Dubon2026
