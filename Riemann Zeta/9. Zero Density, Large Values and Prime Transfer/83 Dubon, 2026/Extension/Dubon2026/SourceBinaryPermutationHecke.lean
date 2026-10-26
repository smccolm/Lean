import Dubon2026.SourceBinaryPrimePowerPermutation
import Dubon2026.SourcePrimeHeckeNaturality
import Dubon2026.SourceBinaryHeckeCohomology

/-! DUB-17/18 -> original all-weight adic association -> finite-level
Hecke realizations. The permutation coefficient evaluation commutes with
the full original prime correspondence on native H1, including its actual
conjugation and coset trace. The existing coefficient naturality theorem
avoids another cochain or Hecke-composition development.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

variable (R : Type) [CommRing R] {Q ell : ℕ} [NeZero ell]

/-- The actual binary diagonal acts on formal vectors and intertwines the
same two original Hecke subgroup actions. -/
theorem sourceBinaryPermutationDiagonal_intertwine (hell : ell.Prime) (w : ℕ)
    (g : heckeUpperSubgroup Q ell) :
    (Finsupp.lmapDomain R R
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : R), 1]))).comp
      ((sourceCoefficientPermutationRep (sourceBinaryCoefficientRep R Q w)).ρ
        (sourceHeckeConjugation hell g)) =
      ((sourceCoefficientPermutationRep (sourceBinaryCoefficientRep R Q w)).ρ g.val).comp
        (Finsupp.lmapDomain R R
          (homogeneousMatrixAction w (Matrix.diagonal ![(ell : R), 1]))) := by
  change (Finsupp.lmapDomain R R
      (homogeneousMatrixAction w (Matrix.diagonal ![(ell : R), 1]))).comp
      (Finsupp.lmapDomain R R
        ((sourceBinaryCoefficientRep R Q w).ρ (sourceHeckeConjugation hell g))) =
    (Finsupp.lmapDomain R R ((sourceBinaryCoefficientRep R Q w).ρ g.val)).comp
      (Finsupp.lmapDomain R R
        (homogeneousMatrixAction w (Matrix.diagonal ![(ell : R), 1])))
  apply Finsupp.lhom_ext
  intro x r
  have h := LinearMap.congr_fun (sourceBinaryHeckeDiagonal_intertwine R hell w g) x
  simpa only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
    congrArg (fun y => Finsupp.single y r) h

/-- The full original Hecke correspondence on permutation coefficients. -/
def sourceBinaryPermutationHeckeH1 (hell : ell.Prime) (w : ℕ) :
    Module.End R (groupCohomology.H1
      (sourceCoefficientPermutationRep (sourceBinaryCoefficientRep R Q w))) :=
  sourcePrimeHeckeH1 hell _
    (Finsupp.lmapDomain R R
      (homogeneousMatrixAction w (Matrix.diagonal ![(ell : R), 1])))
    (sourceBinaryPermutationDiagonal_intertwine R hell w)

/-- Evaluation intertwines the entire original binary H1 Hecke operator,
with no compatibility premise on the original coefficient system. -/
theorem sourceBinaryPermutationHeckeH1_evaluation (hell : ell.Prime) (w : ℕ)
    (x : groupCohomology.H1
      (sourceCoefficientPermutationRep (sourceBinaryCoefficientRep R Q w))) :
    ((groupCohomology.functor R (Gamma0 Q) 1).map
      (sourceCoefficientPermutationEvaluation (sourceBinaryCoefficientRep R Q w)))
        (sourceBinaryPermutationHeckeH1 R hell w x) =
      sourceBinaryHeckeH1 R hell w
        (((groupCohomology.functor R (Gamma0 Q) 1).map
          (sourceCoefficientPermutationEvaluation (sourceBinaryCoefficientRep R Q w))) x) :=
  sourcePrimeHeckeH1_naturality hell _ _
    (sourceCoefficientPermutationEvaluation (sourceBinaryCoefficientRep R Q w))
    _ _ (sourceBinaryPermutationDiagonal_intertwine R hell w)
    (sourceBinaryHeckeDiagonal_intertwine R hell w)
    (sourceCoefficientPermutationEvaluation_linearMap _) x

end
end Dubon2026
