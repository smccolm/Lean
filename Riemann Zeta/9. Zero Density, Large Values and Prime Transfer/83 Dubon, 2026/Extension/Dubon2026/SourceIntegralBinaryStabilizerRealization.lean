import Dubon2026.SourceCoefficientStabilizerCohomology
import Dubon2026.SourceIntegralBinaryPermutationRealization

/-! DUB-17/18 -> original all-weight adic association -> finite-level
geometric realization. The original integral binary H1 class is realized
by actual trivial-coefficient H1 groups of congruence stabilizers. Reuse
the exact finite permutation preimage and its Hecke identities; no claim
that the transported operators are already geometric correspondences,
or that these groups have a constructed arithmetic Galois action.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup
attribute [local instance] sourceCoefficientVectorAction

/-- Every original integral binary H1 class at every positive prime-power
precision comes from the actual congruence-stabilizer H1 groups, retaining
its original prime Hecke transforms under the same comparison. -/
theorem sourceIntegralBinary_exists_stabilizerH1Realization
    (p m Q w : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    let R := ZMod (p ^ (m + 1))
    let A := sourceBinaryCoefficientRep R Q w
    letI : Finite A := sourceBinaryPrimePowerCoefficient_finite p m Q w hp
    letI : Fintype A := Fintype.ofFinite A
    letI : MulAction (Gamma0 Q) A := sourceCoefficientVectorAction A
    (∀ (ω : MulAction.orbitRel.Quotient (Gamma0 Q) A),
      (MulAction.stabilizer (Gamma0 Q) (sourceCoefficientOrbitPoint A ω)).FiniteIndex ∧
      ∀ (g : Gamma0 Q), g.val ∈ Gamma (p ^ (m + 1)) →
        g ∈ MulAction.stabilizer (Gamma0 Q) (sourceCoefficientOrbitPoint A ω)) ∧
    ∀ c : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w),
      ∃ z : (∀ ω : MulAction.orbitRel.Quotient (Gamma0 Q) A,
          groupCohomology.H1 (Rep.trivial R
            (MulAction.stabilizer (Gamma0 Q) (sourceCoefficientOrbitPoint A ω)) R)),
        ((groupCohomology.functor R (Gamma0 Q) 1).map
          (sourceCoefficientPermutationEvaluation A))
          ((sourceCoefficientStabilizerH1Equiv A).symm z) =
            sourceBinaryH1Change (Int.castRingHom R) Q w c ∧
        ∀ (ell : ℕ) (hell : ell.Prime),
          letI : NeZero ell := ⟨hell.ne_zero⟩
          ((groupCohomology.functor R (Gamma0 Q) 1).map
            (sourceCoefficientPermutationEvaluation A))
            (sourceBinaryPermutationHeckeH1 R hell w
              ((sourceCoefficientStabilizerH1Equiv A).symm z)) =
                sourceBinaryH1Change (Int.castRingHom R) Q w
                  (sourceBinaryHeckeH1 ℤ hell w c) := by
  let R := ZMod (p ^ (m + 1))
  let A := sourceBinaryCoefficientRep R Q w
  letI : Finite A := sourceBinaryPrimePowerCoefficient_finite p m Q w hp
  letI : Fintype A := Fintype.ofFinite A
  letI : MulAction (Gamma0 Q) A := sourceCoefficientVectorAction A
  constructor
  · intro ω
    refine ⟨sourceCoefficientOrbitStabilizer_finiteIndex A ω, ?_⟩
    intro g hg
    change g • sourceCoefficientOrbitPoint A ω = sourceCoefficientOrbitPoint A ω
    apply Subtype.ext
    change A.ρ g ω.out = ω.out
    rw [sourceBinaryCoefficientRep_congruence (p ^ (m + 1)) Q w g hg]
    rfl
  · intro c
    obtain ⟨y, hy, hhecke⟩ :=
      (sourceIntegralBinary_exists_primePowerPermutationRealization p m Q w hp hlarge).2.2.2 c
    refine ⟨sourceCoefficientStabilizerH1Equiv A y, ?_, ?_⟩
    · rw [LinearEquiv.symm_apply_apply]
      exact hy
    · intro ell hell
      letI : NeZero ell := ⟨hell.ne_zero⟩
      rw [LinearEquiv.symm_apply_apply]
      exact hhecke ell hell

end
end Dubon2026
