import Dubon2026.SourceHeckeBinaryCohomology

/-! The original primitive eigenform in actual column-binary Hecke cohomology.
DUB-17/18 -> residual modular Galois association -> integral-to-residual
eigensystem reduction. Every original source weight has a nonzero native
binary H1 class with the actual good-prime Fourier eigenvalues. The full
operator has the proved finite-coset formula, not only an action on the
period-image subspace. Residual specialization and Galois association remain open.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The actual column-binary primitive class has its original eigenvalue for the full Hecke correspondence. -/
theorem sourcePrimitive_binaryPeriodCohomology_eigen
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    sourceHeckeBinaryH1 hp (k - 2).toNat (sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm) =
      cuspCoefficients f.toCuspForm p • sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm := by
  change sourcePeriodH1BinaryEquiv (Gamma0 Q) (k - 2).toNat
    (sourceHeckeH1 hp (k - 2).toNat
      ((sourcePeriodH1BinaryEquiv (Gamma0 Q) (k - 2).toNat).symm
        (sourcePeriodH1BinaryEquiv (Gamma0 Q) (k - 2).toNat
          (sourceOriginalPeriodCohomology Q k hk f.toCuspForm)))) = _
  rw [LinearEquiv.symm_apply_apply, sourcePrimitive_periodCohomology_eigen f hk hp hpQ, map_smul]
  rfl

/-- The actual original primitive form supplies a nonzero column-binary H1 eigensystem at all source weights. -/
theorem sourcePrimitive_nonzero_binaryHeckeEigensystem
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p), Nat.Coprime p Q →
        letI : NeZero p := ⟨hp.ne_zero⟩
        sourceHeckeBinaryH1 hp (k - 2).toNat
            (sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm) =
          cuspCoefficients f.toCuspForm p • sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm := by
  refine ⟨sourcePrimitive_binaryPeriodCohomology_ne_zero f hk, ?_⟩
  intro p hp hpQ
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact sourcePrimitive_binaryPeriodCohomology_eigen f hk hp hpQ

end
end Dubon2026
