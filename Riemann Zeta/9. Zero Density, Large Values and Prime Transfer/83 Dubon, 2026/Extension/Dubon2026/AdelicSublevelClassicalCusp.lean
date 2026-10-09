import Dubon2026.AdelicSublevelDescent

/-! # Genuine classical cusp forms at actual finite adelic sublevels -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Holomorphy, every arithmetic cusp condition and the exact actual sublevel slash equations give an actual cusp form at the actual sublevel. -/
theorem adelicAlgebraicFiniteSpan_sublevel_classical_cusp
    (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicFiniteSpan f)
    (hlevel : adelicCyclicHilbertEmbedding f v ∈ adelicSublevelFixedSpace f L) :
    ∃ F : CuspForm ((finiteAdelicSublevelIntegerGroup N L).map (mapGL ℝ)) k,
      realWeightLiftLinear k F = adelicCyclicRealRestriction f v := by
  obtain ⟨F, hF, he⟩ := adelicAlgebraicFiniteSpan_classical_restriction f v hv
  refine ⟨{
    toFun := F
    slash_action_eq' := ?_
    holo' := rationalCuspSlashSpan_holomorphic f F hF
    zero_at_cusps' := fun hc => rationalCuspSlashSpan_zero_at_cusps f F hF
      (hc.mono (Subgroup.map_mono (finiteAdelicSublevelIntegerGroup_le N L))) }, he⟩
  rintro γ ⟨δ, hδ, rfl⟩
  obtain ⟨ε, hε, rfl⟩ := hδ
  exact adelicCyclic_sublevel_classical_slash_invariant f L v hlevel F he ε hε

/-- Every actual finite-adelic Hilbert combination fixed at the actual sublevel has a unique genuine classical cusp restriction. -/
theorem adelicFiniteCyclicSpan_sublevel_classical
    (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicFiniteCyclicSpan f)
    (hlevel : v ∈ adelicSublevelFixedSpace f L) :
    ∃ w ∈ adelicAlgebraicFiniteSpan f, adelicCyclicHilbertEmbedding f w = v ∧
      ∃! F : CuspForm ((finiteAdelicSublevelIntegerGroup N L).map (mapGL ℝ)) k,
        realWeightLiftLinear k F = adelicCyclicRealRestriction f w := by
  obtain ⟨w, hw, he⟩ := adelicFiniteCyclicSpan_preimage f v hv
  have hl : adelicCyclicHilbertEmbedding f w ∈ adelicSublevelFixedSpace f L := he ▸ hlevel
  obtain ⟨F, hF⟩ := adelicAlgebraicFiniteSpan_sublevel_classical_cusp f L w hw hl
  refine ⟨w, hw, he, F, hF, ?_⟩
  intro G hG
  ext z
  exact congrFun (adelicAlgebraicFiniteSpan_classical_unique f w G F hG hF) z

end
end Dubon2026
