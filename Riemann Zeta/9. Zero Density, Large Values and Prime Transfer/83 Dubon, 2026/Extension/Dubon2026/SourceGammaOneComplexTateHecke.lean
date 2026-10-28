import Dubon2026.SourceGammaOnePeriodTateHecke
import Dubon2026.SourceGammaOnePicardPeriodHecke

/-! DUB17/18 -> original all-weight arithmetic realization -> actual
Gamma1 Picard/Tate comparison. The proved literal prime Picard Hecke
compatibility passes to compatible p-power torsion sequences and then
to the scalar extension of the same original integral-period lattice.
No Hecke or finite-basis premise is supplied, and neither the Tate prime
nor the Hecke prime is required to avoid the level. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
open scoped TensorProduct
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
  (hT : ModularGroup.T ∈ Gamma1 M)
local notation "F" => functionFieldOver (Gamma1 M) ℂ
local notation "Λ" => sourceWeightTwoIntegralLattice (Gamma1 M)

theorem complexPicardTatePeriodQuotient_hecke (q : ℕ) [Fact q.Prime]
    (x : TateModule p (Pic0 ℂ F)) :
    TateModule.ofAddEquiv p (picardPeriodEquiv M hT)
        (TateModule.tateMap p (heckePicard ℂ M q) x) =
      TateModule.tateMap p (periodQuotientHecke M q).toAddMonoidHom
        (TateModule.ofAddEquiv p (picardPeriodEquiv M hT) x) := by
  apply Subtype.ext
  funext k
  exact picardPeriodEquiv_hecke M q hT ((x : ℕ → Pic0 ℂ F) k)

theorem complexPicardTatePeriodTensorEquiv_hecke (q : ℕ) [Fact q.Prime]
    (x : TateModule p (Pic0 ℂ F)) :
    complexPicardTatePeriodTensorEquiv M p hT
        (TateModule.tateMap p (heckePicard ℂ M q) x) =
      (periodLatticeHecke M q).baseChange ℤ_[p]
        (complexPicardTatePeriodTensorEquiv M p hT x) := by
  apply (TateModule.Period.phi2 ℂ p Λ (integralPeriodBasis M)).injective
  rw [periodTateTensor_hecke]
  simp only [complexPicardTatePeriodTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact complexPicardTatePeriodQuotient_hecke M p hT q x

end
end Dubon2026.SourceFunctionField.GammaOne
