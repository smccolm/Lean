import Dubon2026.SourceGammaOneHeckePlaceOrbits
import Dubon2026.SourceGammaOneHeckeGeometricSubgroup

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> actual coset
multiplicities. The exact all-point intersection orbit relation transports
through native dilation conjugation to the actual upper subgroup. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup
open scoped MatrixGroups
variable (M d : ℕ) [NeZero M] [NeZero d]

theorem analyticHeckePlace_eq_iff_upper_orbit
    (hH : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (w w₀ : ℍ) :
    analyticPlace hH w = analyticPlace hH w₀ ↔
      levelRaiseMatrix d • w ∈
        MulAction.orbit (sourceGammaOneHeckeUpper M d) (levelRaiseMatrix d • w₀) := by
  rw [HeckeFiberOrbits.analyticHeckePlace_eq_iff_orbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, rfl⟩ := (heckeUpperGeometricEquiv M d).surjective γ
    refine ⟨g⁻¹, ?_⟩
    rw [inv_smul_eq_iff]
    change levelRaiseMatrix d • w₀ = g.val.val • (levelRaiseMatrix d • w)
    rw [← upperToGeometric_smul]
    exact congrArg (levelRaiseMatrix d • ·) hγ.symm
  · rintro ⟨g, hg⟩
    refine ⟨upperToGeometric M d g⁻¹, ?_⟩
    apply (MulAction.injective (levelRaiseMatrix d))
    dsimp only
    rw [upperToGeometric_smul]
    change g⁻¹ • (levelRaiseMatrix d • w) = levelRaiseMatrix d • w₀
    rw [← hg, inv_smul_smul]

end
end Dubon2026.SourceFunctionField.GammaOne
