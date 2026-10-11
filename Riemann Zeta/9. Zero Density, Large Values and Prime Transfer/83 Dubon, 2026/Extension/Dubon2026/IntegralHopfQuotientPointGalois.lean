import Dubon2026.IntegralHopfCoinvariantQuotientPoints
import Dubon2026.HopfQuotientPointCoefficientAction

/-! # Genuine Galois equivariance of the original integral quotient point realization -/

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

/-- The same original source point group in the Galois-equivariant quotient comparison. -/
local instance integralQuotientGaloisSourcePointGroup : CommGroup (WithConv (A →ₐ[R] K)) :=
  finiteFreeHopfPointsCommGroup

/-- The same original subgroup point group in the Galois-equivariant quotient comparison. -/
local instance integralQuotientGaloisSubgroupPointGroup : Group (WithConv (B →ₐ[R] K)) :=
  commutativeHopfPointsGroup

/-- The actual quotient-point realization intertwines every original coefficient automorphism with the genuine coefficient action on the constructed integral invariant Hopf algebra. In particular, this applies to the original Galois automorphisms after restricting scalars. -/
theorem integralHopfCoinvariantQuotientPoints_galois (q : A →ₐc[R] B) (g : K ≃ₐ[R] K) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := integralHopfCoinvariantPointGroup (K := K) q
    ∀ z : WithConv (A →ₐ[R] K) ⧸ (hopfPointsRestriction (K := K) q).range,
      integralHopfCoinvariantQuotientPoints q (hopfQuotientPointCoefficientAutomorphism q g z) =
        commutativeHopfPointsAutomorphism g (integralHopfCoinvariantQuotientPoints q z) := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := integralHopfCoinvariantPointGroup (K := K) q
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    apply WithConv.ext
    ext a
    rfl

end
end Dubon2026
