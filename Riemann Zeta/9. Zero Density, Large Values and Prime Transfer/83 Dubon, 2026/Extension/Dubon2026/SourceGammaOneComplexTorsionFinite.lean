import Dubon2026.SourceGammaOneComplexTatePeriods
import Dubon2026.SourceComplexLatticeTorsion
import Dubon2026.SourceAdditiveTorsionTransport

/-! DUB17/18 -> original all-weight arithmetic realization -> Gamma1
arithmetic/complex Picard torsion comparison -> finite complex torsion.
The proved original Picard-period equivalence and finite free integer
lattice give the exact finite torsion count in terms of its actual
integral rank. No rank-versus-genus identification is assumed or claimed.
This supplies the finite action used in arithmetic torsion descent. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
variable (M : ℕ) [NeZero M]
local notation "F" => functionFieldOver (Gamma1 M) ℂ
local notation "Λ" => sourceWeightTwoIntegralLattice (Gamma1 M)

theorem complex_torsion_cardinality (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion (K := ℂ) («F» := F) n) =
      n ^ Module.finrank ℤ Λ := by
  letI := integralLattice_finite M
  letI := integralLattice_free M
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  change Nat.card (Submodule.torsionBy ℤ (Pic0 ℂ F) (n : ℤ)) = _
  rw [ComplexLatticeTorsion.natCard_torsionBy_congr (picardPeriodEquiv M hT) (n : ℤ)]
  exact ComplexLatticeTorsion.natCard_torsion_quotient Λ n hn

theorem finite_complex_torsion (n : ℕ) (hn : n ≠ 0) :
    Finite (Pic0.torsion (K := ℂ) («F» := F) n) :=
  Nat.finite_of_card_ne_zero (by
    rw [complex_torsion_cardinality M n hn]
    exact pow_ne_zero _ hn)

end
end Dubon2026.SourceFunctionField.GammaOne
