import Dubon2026.SourceBinaryPermutationHeckeWords
import Dubon2026.SourceBinaryH1ModulusKernel

/-! DUB-17/18 -> original all-weight adic association -> geometric finite
Hecke realization. Derive the operator relation needed for descent from
the actual permutation H1 evaluation, full word naturality and the exact
integral reduction kernel. No eigenvector lift or residual H1 integral
lifting assumption is used. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

/-- Every relation on the actual prime-power permutation H1 also holds
in the actual finite image of the original integral H1 Hecke algebra. -/
theorem sourceBinaryPermutationHeckeWord_modulus_zero
    (p n Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p)
    (a : FreeAlgebra ℤ (sourceBinaryHeckePrime Q))
    (ha : FreeAlgebra.lift ℤ
      (sourceBinaryPermutationPrimeOperators (ZMod (p ^ (n + 1))) Q w) a = 0) :
    sourceBinaryH1ModulusOperatorMap Q w (p ^ (n + 1))
      (sourceBinaryH1HeckeWord Q w a) = 0 := by
  apply sourceBinaryH1ModulusOperatorMap_zero_of_coefficients Q w (p ^ (n + 1))
    (pow_ne_zero _ hp.ne_zero)
  intro x
  obtain ⟨y, hy⟩ := sourceBinaryPrimePowerPermutation_H1_surjective p n Q w hp hlarge
    (sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (n + 1)))) Q w x)
  rw [sourceBinaryH1HeckeWord_change, ← hy,
    ← sourceBinaryPermutationHeckeWord_evaluation, ha, LinearMap.zero_apply]
  exact map_zero (((groupCohomology.functor (ZMod (p ^ (n + 1))) (Gamma0 Q) 1).map
    (sourceCoefficientPermutationEvaluation
      (sourceBinaryCoefficientRep (ZMod (p ^ (n + 1))) Q w))).hom)

end
end Dubon2026
