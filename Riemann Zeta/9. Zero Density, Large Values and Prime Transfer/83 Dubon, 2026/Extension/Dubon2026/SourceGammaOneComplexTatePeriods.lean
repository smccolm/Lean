import Dubon2026.SourceGammaOneFinitePeriodLattice
import Dubon2026.SourceTateTorusBasis
import Dubon2026.SourceTateEquivalences

/-! DUB17/18 -> original all-weight arithmetic realization -> actual
Gamma1 Picard/Tate comparison. The proved finite original period lattice
is torsion free, so native PID freeness supplies its finite basis. Apply
the existing Tate-torus theorem to the proved original Picard-period
equivalence. This is the actual complex Picard Tate module; arithmetic
constant-field comparison remains a separate obligation. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
open scoped TensorProduct
variable (M : ℕ) [NeZero M]
local notation "Λ" => sourceWeightTwoIntegralLattice (Gamma1 M)

theorem integralLattice_free : Module.Free ℤ Λ := by
  letI := integralLattice_finite M
  infer_instance

/-- A finite integral basis of the same original Gamma1 period lattice. -/
def integralPeriodBasis : Module.Basis (Fin (Module.finrank ℤ Λ)) ℤ Λ := by
  letI := integralLattice_finite M
  letI := integralLattice_free M
  exact Module.finBasis ℤ Λ

variable (p : ℕ) [Fact p.Prime] (hT : ModularGroup.T ∈ Gamma1 M)

/-- The actual complex Picard Tate module as the p-adic extension of its original period lattice. -/
def complexPicardTatePeriodTensorEquiv :
    TateModule p (Pic0 ℂ (functionFieldOver (Gamma1 M) ℂ)) ≃ₗ[ℤ_[p]]
      ℤ_[p] ⊗[ℤ] Λ :=
  (TateModule.ofAddEquiv p (picardPeriodEquiv M hT)).trans
    (TateModule.Period.phi2 ℂ p Λ (integralPeriodBasis M)).symm

theorem complexPicardTatePeriodTensorEquiv_symm_tmul (a : ℤ_[p]) (l : Λ) :
    TateModule.ofAddEquiv p (picardPeriodEquiv M hT)
        ((complexPicardTatePeriodTensorEquiv M p hT).symm (a ⊗ₜ l)) =
      a • TateModule.Period.iota ℂ p Λ l := by
  simp only [complexPicardTatePeriodTensorEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
    TateModule.Period.phi2_tmul]

end
end Dubon2026.SourceFunctionField.GammaOne
