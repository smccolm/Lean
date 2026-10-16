import Dubon2026.ArithmeticOrbitEqualPrimeTransport
import Dubon2026.ArithmeticOrbitCosetEmbedding

/-! # Equal induced primes lie in the same actual local Galois orbit

Lift the literal comparison of the generated local fields to the original
local algebraic closure. Its restriction to the arithmetic union carries
one original coset to the other. No normality of the finite global field
is assumed. This removes the injectivity premise in DUB-17's prime index.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  (h : rationalArithmeticOrbitPrime a p hp F c = rationalArithmeticOrbitPrime a p hp F c')

/-- The genuine local-closure automorphism extending the equal-prime comparison. -/
def rationalArithmeticOrbitEqualPrimeLift :
    Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) :=
  (rationalArithmeticOrbitEqualPrimeAlgEquiv a p hp F c c' h).liftNormal
    (rationalPrimeLocalClosure p hp)

/-- The lifted automorphism identifies exactly the two coset-twisted original embeddings. -/
theorem rationalArithmeticOrbitEqualPrimeLift_global (x : F) :
    rationalArithmeticOrbitEqualPrimeLift a p hp F c c' h
      (rationalArithmeticOrbitEmbedding a p hp F c (x : rationalUnramifiedExtension a)) =
        rationalArithmeticOrbitEmbedding a p hp F c' (x : rationalUnramifiedExtension a) := by
  have he := (rationalArithmeticOrbitEqualPrimeAlgEquiv a p hp F c c' h).liftNormal_commutes
    (rationalPrimeLocalClosure p hp) (rationalArithmeticOrbitFieldInclusion a p hp F c x)
  change rationalArithmeticOrbitEqualPrimeLift a p hp F c c' h
    (rationalArithmeticOrbitEmbedding a p hp F c (x : rationalUnramifiedExtension a)) = _ at he
  exact he.trans (congrArg (fun y : rationalArithmeticOrbitLocalField a p hp F c' =>
    (y : rationalPrimeLocalClosure p hp))
      (rationalArithmeticOrbitEqualPrimeAlgEquiv_global a p hp F c c' h x))

/-- Equality of the original induced primes forces membership in one actual local Galois orbit. -/
theorem rationalArithmeticOrbitEqualPrimeLift_smul :
    rationalPrimeArithmeticRestriction a p hp
      (rationalArithmeticOrbitEqualPrimeLift a p hp F c c' h) • c = c' :=
  (rationalArithmeticOrbitCoset_smul_iff a p hp F c c'
    (rationalArithmeticOrbitEqualPrimeLift a p hp F c c' h)).mpr
    (rationalArithmeticOrbitEqualPrimeLift_global a p hp F c c' h)

end
end Dubon2026
