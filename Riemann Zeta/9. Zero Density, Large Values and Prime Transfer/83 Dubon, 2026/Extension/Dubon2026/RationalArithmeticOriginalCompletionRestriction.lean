import Dubon2026.RationalArithmeticOriginalCompletionTower
import Dubon2026.ArithmeticOrbitRepresentativeEmbedding
import Dubon2026.OriginalAdicLocalFiniteRelationCup
import Dubon2026.OriginalGlobalCompletionH2

/-! The finite completion's actual Galois restriction agrees with the
original arithmetic restriction at the chosen prime. Both maps are
identified on the original finite field, retaining the actual embedding.
This discharges the group-map edge of DUB-17's Cartier H1 specialization. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The chosen finite arithmetic field retains its given Galois structure. -/
local instance rationalArithmeticOriginalFiniteGalois : IsGalois ℚ F := F.isGalois

/-- The chosen completed finite-field embedding is literally the original
arithmetic embedding at the identity coset. -/
theorem rationalArithmeticOriginalCompletion_global (x : F) :
    algebraMap ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
      (algebraMap F ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) x) =
      rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a
        (x : rationalUnramifiedExtension a) := by
  have h := rationalArithmeticOrbitEmbedding_mk a p hp F.toIntermediateField 1 x
  exact (rationalArithmeticOrbitCompletionEquiv_coe a p hp F.toIntermediateField
    (QuotientGroup.mk 1) x).trans h

/-- The literal finite completion restriction is the restriction of the
original prime-local arithmetic automorphism to the same finite field. -/
theorem rationalArithmeticOriginalCompletion_galois_restriction
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)
      (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        (rationalPrimeLocalField p hp)
        ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp) g) =
      AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp g) := by
  let W := (rationalArithmeticOriginalPrime a p hp F).adicCompletion F
  let Ω₀ := rationalPrimeLocalClosure p hp
  let h := galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    (rationalPrimeLocalField p hp) W Ω₀ g
  let e := rationalArithmeticLocalEmbedding (K := Ω₀) a
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  apply e.injective
  change e ((originalCompletionGaloisRestriction ℚ F (rationalOriginalPrimePlace p hp)
    (rationalArithmeticOriginalPrime a p hp F) h x : F) : rationalUnramifiedExtension a) =
    e (((AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp g)) x : F) :
      rationalUnramifiedExtension a)
  calc
    e ((originalCompletionGaloisRestriction ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F) h x : F) : rationalUnramifiedExtension a) =
      algebraMap W Ω₀ (algebraMap F W
        (originalCompletionGaloisRestriction ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F) h x)) :=
      (rationalArithmeticOriginalCompletion_global a p hp F _).symm
    _ = g (algebraMap W Ω₀ (algebraMap F W x)) := by
      rw [originalCompletionGaloisRestriction_commutes]
      exact galoisBaseChangeRestriction_commutes
        ((rationalOriginalPrimePlace p hp).adicCompletion ℚ) (rationalPrimeLocalField p hp) W Ω₀ g _
    _ = g (e (x : rationalUnramifiedExtension a)) :=
      congrArg g (rationalArithmeticOriginalCompletion_global a p hp F x)
    _ = e (((AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp g)) x : F) :
        rationalUnramifiedExtension a) :=
      (rationalPrimeArithmeticRestriction_commutes a p hp g (x : rationalUnramifiedExtension a)).symm.trans
        (congrArg e ((show Gal(rationalUnramifiedExtension a / ℚ) from
          rationalPrimeArithmeticRestriction a p hp g).restrictNormal_commutes F x)).symm

end
end Dubon2026
