import Dubon2026.SourceBinaryHeckeChange
import Dubon2026.SourcePrimitiveBinaryHeckeCohomology

/-! Identify the integral-model Hecke operator with the original analytic one.
DUB-17/18 -> residual modular Galois association -> integral-to-residual H1
eigensystem -> the original complex Hecke eigenclass. Both full operators
have the same literal coset formula, so equality holds on the full native H1.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable {Q p : ℕ} [NeZero p] (hp : Nat.Prime p) (w : ℕ)

/-- The coefficient-ring Hecke operator equals the original transported analytic operator on every cocycle. -/
theorem sourceBinaryHeckeCocycle_complex :
    sourceBinaryHeckeCocycle (Q := Q) ℂ hp w = sourceHeckeBinaryCocycle hp w := by
  apply LinearMap.ext
  intro c
  apply groupCohomology.cocycles₁_ext
  intro g
  rw [sourceBinaryHeckeCocycle_apply, sourceHeckeBinaryCocycle_apply]

/-- The full coefficient-ring binary H1 Hecke operator is the original analytic Hecke correspondence. -/
theorem sourceBinaryHeckeH1_complex :
    sourceBinaryHeckeH1 (Q := Q) ℂ hp w = sourceHeckeBinaryH1 hp w := by
  apply LinearMap.ext
  intro x
  refine groupCohomology.H1_induction_on x ?_
  intro c
  rw [sourceBinaryHeckeH1_cocycle, sourceHeckeBinaryH1_cocycle,
    sourceBinaryHeckeCocycle_complex]

omit [NeZero p] in
/-- The actual original primitive form gives a nonzero eigenclass for the complex specialization
of the integral-model full Hecke action, at every source weight and every good prime. -/
theorem sourcePrimitive_nonzero_integralModelComplexEigensystem
    [NeZero Q] {k : ℤ} (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm ≠ 0 ∧
      ∀ (l : ℕ) (hl : Nat.Prime l), Nat.Coprime l Q →
        letI : NeZero l := ⟨hl.ne_zero⟩
        sourceBinaryHeckeH1 ℂ hl (k - 2).toNat
            (sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm) =
          cuspCoefficients f.toCuspForm l • sourceOriginalBinaryPeriodCohomology Q k hk f.toCuspForm := by
  obtain ⟨hne, heig⟩ := sourcePrimitive_nonzero_binaryHeckeEigensystem f hk
  refine ⟨hne, ?_⟩
  intro l hl hlQ
  letI : NeZero l := ⟨hl.ne_zero⟩
  rw [sourceBinaryHeckeH1_complex]
  exact heig l hl hlQ

end
end Dubon2026
