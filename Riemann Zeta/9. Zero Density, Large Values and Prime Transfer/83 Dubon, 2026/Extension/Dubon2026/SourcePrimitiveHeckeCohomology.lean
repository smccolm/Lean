import Dubon2026.SourcePeriodHeckeCohomology
import Dubon2026.SourcePeriodCohomologyInjective
import Dubon2026.HeckeAllIndices

/-! The actual nonzero primitive Hecke eigenclass in native H1.
DUB-17/18 -> residual modular Galois association -> original integral and
residual Hecke eigensystem. Analytic Hecke compatibility and the previously
proved all-weight injectivity discharge the complex eigenclass input.
Coefficient-convention compatibility of Hecke, residual nonvanishing and
the geometric Galois construction remain separate obligations.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup OnePoint
open scoped MatrixGroups

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The original Gamma0 period map intertwines the actual analytic and full H1 prime operators. -/
theorem sourceOriginalPeriodCohomology_hecke (hk : 2 ≤ k)
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    sourceOriginalPeriodCohomology Q k hk (cuspHeckePrime hp f) =
      sourceHeckeH1 hp (k - 2).toNat (sourceOriginalPeriodCohomology Q k hk f) :=
  sourcePeriodH1_hecke (w := (k - 2).toNat) hp hpQ f (by omega) ∞

/-- The actual primitive H1 class has its original Fourier eigenvalue at every good prime. -/
theorem sourcePrimitive_periodCohomology_eigen
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    sourceHeckeH1 hp (k - 2).toNat (sourceOriginalPeriodCohomology Q k hk f.toCuspForm) =
      cuspCoefficients f.toCuspForm p • sourceOriginalPeriodCohomology Q k hk f.toCuspForm := by
  rw [← sourceOriginalPeriodCohomology_hecke hk hp hpQ]
  have he := primitiveCuspForm_eigenvector f hp.pos hpQ
  rw [cuspHeckeLinear_prime Q k hp] at he
  change cuspHeckePrime hp f.toCuspForm = _ at he
  rw [he, _root_.map_smul]

/-- An actual original primitive form supplies a nonzero native H1 eigensystem at every source weight. -/
theorem sourcePrimitive_nonzero_periodHeckeEigensystem
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalPeriodCohomology Q k hk f.toCuspForm ≠ 0 ∧
      ∀ (p : ℕ) (hp : Nat.Prime p), Nat.Coprime p Q →
        letI : NeZero p := ⟨hp.ne_zero⟩
        sourceHeckeH1 hp (k - 2).toNat (sourceOriginalPeriodCohomology Q k hk f.toCuspForm) =
          cuspCoefficients f.toCuspForm p • sourceOriginalPeriodCohomology Q k hk f.toCuspForm := by
  refine ⟨sourcePrimitive_periodCohomology_ne_zero f hk, ?_⟩
  intro p hp hpQ
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact sourcePrimitive_periodCohomology_eigen f hk hp hpQ

end
end Dubon2026
