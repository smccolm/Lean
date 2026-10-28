import Dubon2026.SourceModularSmoothedFundamental

/-! Actual original Gamma1 specialization of the compact smooth orbit partition.
This supplies the cutoff hypotheses for the winding-period limit serving
DUB-17/18 through the original Picard/H1 and Abel-Jacobi chain. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane SourceSmoothedFundamental
open scoped MatrixGroups Topology ContDiff

theorem sourceGamma1_smooth_partition (N : ℕ) [NeZero N] (T : ℝ) :
    (∀ n : ℕ∞, ContDiff ℝ n (smoothedFundamental (CongruenceSubgroup.Gamma1 N) T)) ∧
    HasCompactSupport (smoothedFundamental (CongruenceSubgroup.Gamma1 N) T) ∧
    tsupport (smoothedFundamental (CongruenceSubgroup.Gamma1 N) T) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 ≤ smoothedFundamental (CongruenceSubgroup.Gamma1 N) T z) ∧
    (∀ τ : ℍ, (Function.support fun γ : (CongruenceSubgroup.Gamma1 N) =>
        smoothedFundamental (CongruenceSubgroup.Gamma1 N) T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite) ∧
    (∀ τ : ℍ,
      ∑ᶠ γ : (CongruenceSubgroup.Gamma1 N), smoothedFundamental (CongruenceSubgroup.Gamma1 N) T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) ≤ 1) ∧
    (∀ τ : ℍ, max τ.im τ.im⁻¹ ≤ T →
      ∑ᶠ γ : (CongruenceSubgroup.Gamma1 N), smoothedFundamental (CongruenceSubgroup.Gamma1 N) T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 1) ∧
    (∃ G : Finset SL(2, ℤ), ∀ δ : SL(2, ℤ), δ ∉ G → ∀ τ : ℍ,
      smoothedFundamental (CongruenceSubgroup.Gamma1 N) T τ ≠ 0 →
        smoothedFundamental (CongruenceSubgroup.Gamma1 N) T ((δ • τ : ℍ) : ℂ) = 0) :=
  smooth_partition (CongruenceSubgroup.Gamma1 N) T

end
end Dubon2026
