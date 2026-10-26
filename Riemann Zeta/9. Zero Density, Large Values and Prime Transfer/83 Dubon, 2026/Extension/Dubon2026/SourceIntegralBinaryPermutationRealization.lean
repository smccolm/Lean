import Dubon2026.SourceBinaryPermutationHecke
import Dubon2026.SourceBinaryPermutationCongruence
import Dubon2026.SourceBinaryHeckeChange

/-! DUB-17/18 -> original all-weight adic association -> compatible
prime-power Hecke realizations. Every class in the original integral
binary H1 has an actual finite-permutation realization modulo each positive
prime power. Evaluation retains its original prime Hecke transforms and
the principal congruence subgroup acts trivially on the coefficient terms.
This does not assert that a chosen preimage is an eigenvector, nor does it
construct an arithmetic Galois action or a compatible characteristic-zero
specialization. Those are the remaining steps on this route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

/-- The original integral binary cohomology, at every degree and positive
prime-power precision, is realized by finite congruence permutation
coefficients with exact evaluation of all its original prime Hecke transforms. -/
theorem sourceIntegralBinary_exists_primePowerPermutationRealization
    (p m Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    Finite (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w) ∧
    Module.Finite (ZMod (p ^ (m + 1)))
      (sourceCoefficientPermutationRep
        (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w)) ∧
    (∀ (g : Gamma0 Q), g.val ∈ Gamma (p ^ (m + 1)) →
      (sourceCoefficientPermutationRep
        (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w)).ρ g = 1) ∧
    ∀ c : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w),
      ∃ y : groupCohomology.H1 (sourceCoefficientPermutationRep
        (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w)),
        ((groupCohomology.functor (ZMod (p ^ (m + 1))) (Gamma0 Q) 1).map
          (sourceCoefficientPermutationEvaluation
            (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w))) y =
          sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (m + 1)))) Q w c ∧
        ∀ (ell : ℕ) (hell : ell.Prime),
          letI : NeZero ell := ⟨hell.ne_zero⟩
          ((groupCohomology.functor (ZMod (p ^ (m + 1))) (Gamma0 Q) 1).map
            (sourceCoefficientPermutationEvaluation
              (sourceBinaryCoefficientRep (ZMod (p ^ (m + 1))) Q w)))
              (sourceBinaryPermutationHeckeH1 (ZMod (p ^ (m + 1))) hell w y) =
            sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (m + 1)))) Q w
              (sourceBinaryHeckeH1 ℤ hell w c) := by
  refine ⟨sourceBinaryPrimePowerCoefficient_finite p m Q w hp,
    sourceBinaryPrimePowerPermutation_finite p m Q w hp,
    sourceBinaryPermutationRep_congruence (p ^ (m + 1)) Q w, ?_⟩
  intro c
  obtain ⟨y, hy⟩ := sourceBinaryPrimePowerPermutation_H1_surjective p m Q w hp hlarge
    (sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (m + 1)))) Q w c)
  refine ⟨y, hy, ?_⟩
  intro ell hell
  letI : NeZero ell := ⟨hell.ne_zero⟩
  rw [sourceBinaryPermutationHeckeH1_evaluation, hy, sourceBinaryH1Change_hecke]

end
end Dubon2026
