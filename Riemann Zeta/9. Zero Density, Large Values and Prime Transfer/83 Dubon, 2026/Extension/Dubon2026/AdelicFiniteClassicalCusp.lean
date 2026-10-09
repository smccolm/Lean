import Dubon2026.AdelicCyclicLevelDescent

/-! # Genuine original-level classical cusp forms reconstructed from fixed finite-adelic combinations -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Holomorphy, every arithmetic cusp condition and the exact original slash equations give an actual cusp form at the original level. -/
theorem adelicAlgebraicFiniteSpan_classical_cusp
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicFiniteSpan f)
    (hlevel : adelicCyclicHilbertEmbedding f v ∈ adelicLevelFixedSpace f) :
    ∃ F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
      realWeightLiftLinear k F = adelicCyclicRealRestriction f v := by
  obtain ⟨F, hF, he⟩ := adelicAlgebraicFiniteSpan_classical_restriction f v hv
  refine ⟨{
    toFun := F
    slash_action_eq' := ?_
    holo' := rationalCuspSlashSpan_holomorphic f F hF
    zero_at_cusps' := fun hc => rationalCuspSlashSpan_zero_at_cusps f F hF hc }, he⟩
  rintro γ ⟨δ, hδ, rfl⟩
  exact adelicCyclic_classical_slash_invariant f v hlevel F he ⟨δ, hδ⟩

/-- Every actual finite-adelic Hilbert combination fixed at the original level has a unique genuine classical cusp restriction. -/
theorem adelicFiniteCyclicSpan_fixed_classical
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicFiniteCyclicSpan f)
    (hlevel : v ∈ adelicLevelFixedSpace f) :
    ∃ w ∈ adelicAlgebraicFiniteSpan f, adelicCyclicHilbertEmbedding f w = v ∧
      ∃! F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
        realWeightLiftLinear k F = adelicCyclicRealRestriction f w := by
  obtain ⟨w, hw, he⟩ := adelicFiniteCyclicSpan_preimage f v hv
  have hl : adelicCyclicHilbertEmbedding f w ∈ adelicLevelFixedSpace f := he ▸ hlevel
  obtain ⟨F, hF⟩ := adelicAlgebraicFiniteSpan_classical_cusp f w hw hl
  refine ⟨w, hw, he, F, hF, ?_⟩
  intro G hG
  ext z
  exact congrFun (adelicAlgebraicFiniteSpan_classical_unique f w G F hG hF) z

end
end Dubon2026
