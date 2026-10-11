import Dubon2026.HopfCoinvariantBaseChange
import Dubon2026.HopfCoinvariantCoordinateAlgebra
import Dubon2026.BialgebraCoordinateComparison
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Genuine Hopf coordinate equivalence between scalar-extended invariants and extended-coordinate invariants -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

section Algebra

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]

/-- The literal scalar extension of the original invariant algebra is equivalent to the actual invariants of the extended subgroup coordinate map. Injectivity follows from flatness and surjectivity from the proved exact equalizer range. -/
def hopfCoinvariantBaseChangeAlgEquiv (q : A →ₐc[R] B) :
    S ⊗[R] hopfSubgroupCoinvariants q ≃ₐ[S]
      hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := S) q) :=
  (AlgEquiv.ofInjective
    (Algebra.TensorProduct.map (AlgHom.id S S) (hopfSubgroupCoinvariants q).val)
    (algebraEqualizerBaseChange_injective (hopfSubgroupRightCoaction q)
      Algebra.TensorProduct.includeLeft)).trans
    (Subalgebra.equivOfEq _ _ (hopfCoinvariantBaseChange_range q))

/-- The genuine invariant base-change equivalence retains the exact original ambient coordinate inclusion on every tensor. -/
theorem hopfCoinvariantBaseChangeAlgEquiv_coordinate (q : A →ₐc[R] B)
    (z : S ⊗[R] hopfSubgroupCoinvariants q) :
    (hopfCoinvariantBaseChangeAlgEquiv q z).val =
      (Algebra.TensorProduct.map (AlgHom.id S S) (hopfSubgroupCoinvariants q).val) z := by
  rfl

end Algebra

section Hopf

variable {R K A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field K] [Algebra R K] [Module.Flat R K]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]
  [CommRing B] [HopfAlgebra R B] [Module.Free R B]

/-- The actual scalar-extended integral invariant Hopf algebra and the actual invariant Hopf algebra of the geometric coordinates are genuinely equivalent as bialgebras. Their original ambient inclusions derive the coalgebra compatibility. -/
def hopfCoinvariantBaseChangeBialgEquiv (q : A →ₐc[R] B) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := hopfCoinvariantHopfAlgebra (hopfBaseChangeCoordinateMap (S := K) q)
    K ⊗[R] hopfSubgroupCoinvariants q ≃ₐc[K]
      hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q) := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := hopfCoinvariantHopfAlgebra (hopfBaseChangeCoordinateMap (S := K) q)
  letI : Module.Free K (hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := K) q)) :=
    (hopfSubgroupCoinvariants_finite_free (hopfBaseChangeCoordinateMap (S := K) q)).2
  let i := hopfCoinvariantBialgebraInclusion (hopfBaseChangeCoordinateMap (S := K) q)
  let j := Bialgebra.TensorProduct.map (BialgHom.id K K) (hopfCoinvariantBialgebraInclusion q)
  apply bialgebraCoordinateComparison i Subtype.val_injective j
    (hopfCoinvariantBaseChangeAlgEquiv q)
  apply AlgHom.ext
  intro z
  exact hopfCoinvariantBaseChangeAlgEquiv_coordinate q z

/-- The genuine invariant Hopf base-change comparison evaluates the original pure tensor in the same original ambient coordinates. -/
theorem hopfCoinvariantBaseChangeBialgEquiv_tmul (q : A →ₐc[R] B)
    (k : K) (a : hopfSubgroupCoinvariants q) :
    (hopfCoinvariantBaseChangeBialgEquiv q (k ⊗ₜ[R] a)).val = k ⊗ₜ[R] a.val := by
  rfl

/-- The actual base-change equivalence preserves inversion on the genuine constructed invariant Hopf coordinate algebras. -/
theorem hopfCoinvariantBaseChangeBialgEquiv_antipode (q : A →ₐc[R] B)
    (z : K ⊗[R] hopfSubgroupCoinvariants q) :
    letI := hopfCoinvariantHopfAlgebra q
    letI := hopfCoinvariantHopfAlgebra (hopfBaseChangeCoordinateMap (S := K) q)
    hopfCoinvariantBaseChangeBialgEquiv q (HopfAlgebra.antipode K z) =
      HopfAlgebra.antipode K (hopfCoinvariantBaseChangeBialgEquiv q z) := by
  letI := hopfCoinvariantHopfAlgebra q
  letI := hopfCoinvariantHopfAlgebra (hopfBaseChangeCoordinateMap (S := K) q)
  exact hopfCoordinateMap_antipode (hopfCoinvariantBaseChangeBialgEquiv q).toBialgHom z

end Hopf
end
end Dubon2026
